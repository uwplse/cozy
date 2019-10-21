"""Classes for managing "contexts".

A Context object describes in-scope variables and functions.

Each variable is one of
 - a "state variable" (part of the data structure state)
 - an "argument variable" (a formal parameter to a method call)
 - a "binder" (a bound variable introduced in a lambda)

Each function is uninterpreted; the Context only cares about their type
signatures, not their definitions.  Functions live in a different namespace from
variables---that is, a function may have the same name as a variable without
confusion.  Functions do not have the same state/argument/binder distinction as
variables; since functions are not first-class objects in Cozy's language, they
cannot come from formal parameters or bound variables in lambdas.

An example helps illustrate the meaning of a context.  Consider this Cozy
specification:

    state xs : Bag<Int>

    query q(i : Int)
        [x+1 | x <- xs, x > i]

The expression `x+1` lives in a context where
    xs is a state variable
    i is an argument variable
    x is a binder and is always an element of xs

Important terminology:
 - "root context": a context where there are no binders
 - "legal": an expression is "legal" in a context if all the free variables in
   the expression are described by the context
 - "more general": a context A is "more general" than another context B if it
   describes only a subset of B's variables

Important functions:
 - all_subexpressions_with_context_information: enumerate all subexpressions
   (with corresponding context and pool) of a given top-level expression.
   (See pools.py for a description of pools in Cozy.)
 - replace: context-aware expression replacement.
"""

from collections import OrderedDict
import itertools

from cozy.common import OrderedSet, unique, Visitor, save_property
from cozy.syntax import TFunc, TBag, Exp, EVar, EAll, ESingleton
from cozy.target_syntax import EDeepIn
from cozy.evaluation import eval
from cozy.syntax_tools import pprint, alpha_equivalent, free_vars, subst, BottomUpRewriter
from cozy.pools import Pool, RUNTIME_POOL, STATE_POOL

class Context(object):
    """A Context describes each variable in the environment.

    A Context is hashable and comparable---but note that equality (==) is
    stricter than alpha equivalence (see `Context.alpha_equivalent`).
    """

    def vars(self) -> {(EVar, Pool)}:
        """Return all in-scope variables (and what pools they are legal in)"""
        raise NotImplementedError()

    def funcs(self) -> {str:TFunc}:
        """Return all in-scope functions and their types"""
        raise NotImplementedError()

    def parent(self):
        """
        If this context is underneath a binder, return the context outside the
        binder.  Otherwise (if this is a root context) return None.
        """
        raise NotImplementedError()

    def root(self):
        """Return this context's root context."""
        ctx = self
        while ctx.parent() is not None:
            ctx = ctx.parent()
        return ctx

    def complexity(self):
        """Return the number of steps to the root context"""
        n = 0
        ctx = self
        while ctx is not None:
            n += 1
            ctx = ctx.parent()
        return n

    def legal_for(self, fvs : {EVar}) -> bool:
        """
        Determine whether an expression containing the given free variables is
        legal in this context.
        """
        vs = {(v, v.type) for (v, pool) in self.vars()}
        return all((v, v.type) in vs for v in fvs)

    def instantiate_examples(self, examples : [dict]) -> [dict]:
        """
        Given a set of examples (mappings from variables to values) for the
        root context, produce a set of examples that include all variables in
        this context.
        """
        raise NotImplementedError()

    def alpha_equivalent(self, other) -> bool:
        """Determine whether this context is alpha equivalent to another.

        For instance, consider the context for variable "x" and "y" in each of
        these larger expressions:

            Map {x -> x+1} xs         (1)
                      ^

            Map {y -> y+1} xs         (2)
                      ^

        Those contexts are
            x in xs
        and
            y in xs.

        If we alpha-rename x to y (or vice-versa), these are the same context.
        """
        raise NotImplementedError()

    def adapt(self, e : Exp, ctx, e_fvs : {EVar} = None) -> Exp:
        """
        If expression `e` is legal in context `ctx` and this context is
        alpha-equivalent to `ctx`, produce an expression equivalent to `e` but
        legal in this context.
        """
        raise NotImplementedError()

    def path_conditions(self) -> [Exp]:
        """Return a set of true facts about this context.

        For instance, in the context where x is a binder and always an element
        of a collection xs, "x in xs" is a path condition.
        """
        raise NotImplementedError()

    def path_condition(self) -> Exp:
        """Return an expression capturing all of self.path_conditions()"""
        return EAll(self.path_conditions())

    def generalize(self, fvs : {EVar}):
        """
        Return the most general context that an expression with the given free
        variables would be legal in.
        """
        raise NotImplementedError()

class RootCtx(Context):
    def __init__(self, state_vars : [Exp] = (), args : [Exp] = (), funcs : {str:TFunc} = None):
        """Construct a root context.

        Parameters:
            state_vars - state variables in scope
            args - argument variables in scope
            funcs - functions in scope

        The sets of state variables and arguments must be disjoint.
        """
        self.state_vars = OrderedSet(state_vars)
        self.args = OrderedSet(args)
        self.functions = OrderedDict(funcs or ())
        assert not (self.state_vars & self.args)
    def vars(self):
        return OrderedSet(itertools.chain(
            [(v, STATE_POOL)   for v in self.state_vars],
            [(v, RUNTIME_POOL) for v in self.args]))
    def funcs(self):
        return self.functions
    def parent(self):
        return None
    def instantiate_examples(self, examples : [dict]) -> [dict]:
        return examples
    def alpha_equivalent(self, other):
        return self == other
    def adapt(self, e : Exp, ctx, e_fvs=None) -> Exp:
        if self == ctx:
            return e
        raise Exception("cannot adapt from {} to {}".format(ctx, self))
    def path_conditions(self):
        return []
    def generalize(self, fvs):
        return self
    def __hash__(self):
        return hash((tuple(self.state_vars), tuple(self.args)))
    def __eq__(self, other):
        return isinstance(other, RootCtx) and (self.state_vars, self.args) == (other.state_vars, other.args)
    def __repr__(self):
        return "RootCtx(state_vars={!r}, args={!r}, funcs={!r})".format(self.state_vars, self.args, self.functions)
    def __str__(self):
        return "(root)"

class UnderBinder(Context):
    def __init__(self, parent : Context, v : EVar, bag : Exp, bag_pool : Pool):
        """Construct a context under a binder.

        Parameters:
            parent - the context of the enclosing lambda
            v - the bound variable
            bag - the bag that v must be a member of
            bag_pool - the pool that the bag belongs to

        `v`'s type annotation must be the same as the type of elements
        in the bag.

        `bag` must be legal in the parent context.

        `v` must not already be described by the parent context.
        """
        assert v.type == bag.type.elem_type, "%s, %s" % (v.type, bag.type)
        assert parent.legal_for(free_vars(bag)), "cannot create context for {} in {}, {}".format(v.id, pprint(bag), parent)
        assert not any(v == vv for vv, p in parent.vars()), "binder {} already free in {}".format(v.id, parent)
        self._parent = parent
        self.var = v
        self.bag = bag
        self.pool = bag_pool
    def vars(self):
        return self._parent.vars() | {(self.var, self.pool)}
    def funcs(self):
        return self._parent.funcs()
    def parent(self):
        return self._parent
    def instantiate_examples(self, examples : [dict]) -> [dict]:
        inst = self._parent.instantiate_examples(examples)
        res = []
        for ex in inst:
            vals = eval(self.bag, ex)
            for v in unique(vals):
                ex = dict(ex)
                ex[self.var.id] = v
                res.append(ex)
        return res
    def alpha_equivalent(self, other):
        if not isinstance(other, UnderBinder):
            return False
        if self.pool != other.pool:
            return False
        if not self.var.type == other.var.type:
            return False
        if not self._parent.alpha_equivalent(other._parent):
            return False
        return alpha_equivalent(self.bag, self._parent.adapt(other.bag, other._parent))
    def adapt(self, e : Exp, ctx, e_fvs=None) -> Exp:
        if self == ctx:
            return e
        if e_fvs is None:
            e_fvs = free_vars(e)
        if isinstance(ctx, UnderBinder):
            if ctx.var not in e_fvs:
                return self.adapt(e, ctx.parent(), e_fvs=e_fvs)
            if alpha_equivalent(self.bag, self._parent.adapt(ctx.bag, ctx._parent)):
                e = self._parent.adapt(e, ctx._parent, e_fvs=e_fvs)
                return subst(e, { ctx.var.id : self.var })
        return self._parent.adapt(e, ctx, e_fvs=e_fvs)
    def path_conditions(self):
        pcs = self._parent.path_conditions()
        # pcs = [pc for pc in self._parent.path_conditions() if self.var not in free_vars(pc)]
        pcs.append(EDeepIn(self.var, self.bag))
        return pcs
    def generalize(self, fvs):
        if self.var not in fvs:
            return self._parent.generalize(fvs)
        new_parent = self._parent.generalize(fvs - { self.var } | free_vars(self.bag))
        if new_parent is self._parent:
            return self
        return UnderBinder(
            new_parent,
            self.var,
            self.bag,
            self.pool)
    def __hash__(self):
        return hash((self._parent, self.var, self.bag, self.pool))
    def __eq__(self, other):
        return isinstance(other, UnderBinder) and (self._parent, self.var, self.bag, self.pool) == (other._parent, other.var, other.bag, other.pool)
    def __repr__(self):
        return "UnderBinder(parent={!r}, v={!r}, bag={!r}, bag_pool={!r})".format(self._parent, self.var, self.bag, self.pool)
    def __str__(self):
        return "{} in {}, {}".format(self.var.id, pprint(self.bag), self._parent)

class _Shredder(Visitor):
    """Helper for all_subexpressions_with_context_information."""
    def __init__(self, ctx, pool=RUNTIME_POOL):
        self.root_ctx = ctx
        self.ctx = ctx
        self.pool = pool
    def visit_ELambda(self, e, bag):
        with save_property(self, "ctx"):
            self.ctx = UnderBinder(self.ctx, e.arg, bag, self.pool)
            yield from self.visit(e.body)
    def visit_EStateVar(self, e):
        yield (e, self.ctx, self.pool)
        with save_property(self, "pool"):
            with save_property(self, "ctx"):
                self.pool = STATE_POOL
                self.ctx = self.root_ctx
                yield from self.visit(e.e)
    def visit_EMap(self, e):
        yield (e, self.ctx, self.pool)
        yield from self.visit(e.e)
        yield from self.visit(e.transform_function, e.e)
    def visit_EFilter(self, e):
        yield (e, self.ctx, self.pool)
        yield from self.visit(e.e)
        yield from self.visit(e.predicate, e.e)
    def visit_EFlatMap(self, e):
        yield (e, self.ctx, self.pool)
        yield from self.visit(e.e)
        yield from self.visit(e.transform_function, e.e)

    def visit_ESorted(self, e):
        yield (e, self.ctx, self.pool)
        yield from self.visit(e.e)
        yield from self.visit(e.asc)

    def visit_EArgMin(self, e):
        yield (e, self.ctx, self.pool)
        yield from self.visit(e.e)
        yield from self.visit(e.key_function, e.e)
    def visit_EArgMax(self, e):
        yield (e, self.ctx, self.pool)
        yield from self.visit(e.e)
        yield from self.visit(e.key_function, e.e)
    def visit_EMakeMap2(self, e):
        yield (e, self.ctx, self.pool)
        yield from self.visit(e.e)
        yield from self.visit(e.value_function, e.e)
    def visit_EMakeMinHeap(self, e):
        yield (e, self.ctx, self.pool)
        yield from self.visit(e.e)
        yield from self.visit(e.key_function, e.e)
    def visit_EMakeMaxHeap(self, e):
        yield (e, self.ctx, self.pool)
        yield from self.visit(e.e)
        yield from self.visit(e.key_function, e.e)
    def visit_ELet(self, e):
        yield (e, self.ctx, self.pool)
        yield from self.visit(e.e)
        yield from self.visit(e.body_function, ESingleton(e.e).with_type(TBag(e.e.type)))
    def visit_Exp(self, e):
        yield (e, self.ctx, self.pool)
        for child in e.children():
            yield from self.visit(child)
    def visit_tuple(self, t):
        for x in t:
            yield from self.visit(x)
    def visit_str(self, s):
        return ()
    def visit_int(self, i):
        return ()
    def visit_float(self, i):
        return ()
    def visit_Fraction(self, i):
        return ()

def all_subexpressions_with_context_information(e : Exp, context : Context, pool : Pool = RUNTIME_POOL) -> [(Exp, Context, Pool)]:
    """Iterate over all subexpressions in `e`.

    This function returns a stream of (exp, context, pool) tuples, where `exp`
    is a subexpression of `e` described by `context` and `pool`.

    The tuple describing the top-level expression (e, context, pool) is
    included in the returned stream.
    """
    return _Shredder(context, pool).visit(e)

def _sametype(e1 : Exp, e2 : Exp):
    if hasattr(e1, "type") and hasattr(e2, "type"):
        return e1.type == e2.type
    return True

class _Replacer(BottomUpRewriter):
    """Helper for replace."""
    def __init__(self,
            haystack_context : Context,
            haystack_pool : Pool,
            needle : Exp,
            needle_context : Context,
            needle_pool : Pool,
            replacement : Exp):
        self.ctx = haystack_context
        self.root_ctx = haystack_context
        self.pool = RUNTIME_POOL
        self.needle = needle
        self.needle_context = needle_context
        self.needle_pool = needle_pool
        self.replacement = replacement
    def visit_ELambda(self, e, bag):
        with save_property(self, "ctx"):
            self.ctx = UnderBinder(self.ctx, e.arg, bag, self.pool)
            new_body = self.visit(e.body)
        return self.join(e, (e.arg, new_body))
    def visit_EStateVar(self, e):
        with save_property(self, "pool"):
            with save_property(self, "ctx"):
                self.pool = STATE_POOL
                self.ctx = self.root_ctx
                ee = self.visit(e.e)
        return self.join(e, (ee,))
    def visit_EMap(self, e):
        return self.join(e, (self.visit(e.e), self.visit(e.transform_function, e.e)))
    def visit_EFilter(self, e):
        return self.join(e, (self.visit(e.e), self.visit(e.predicate, e.e)))
    def visit_EFlatMap(self, e):
        return self.join(e, (self.visit(e.e), self.visit(e.transform_function, e.e)))
    def visit_EArgMin(self, e):
        return self.join(e, (self.visit(e.e), self.visit(e.key_function, e.e)))
    def visit_EArgMax(self, e):
        return self.join(e, (self.visit(e.e), self.visit(e.key_function, e.e)))
    def visit_EMakeMap2(self, e):
        return self.join(e, (self.visit(e.e), self.visit(e.value_function, e.e)))
    def visit_EMakeMinHeap(self, e):
        return self.join(e, (self.visit(e.e), self.visit(e.key_function, e.e)))
    def visit_EMakeMaxHeap(self, e):
        return self.join(e, (self.visit(e.e), self.visit(e.key_function, e.e)))
    def visit_ELet(self, e):
        return self.join(e, (self.visit(e.e), self.visit(e.body_function, ESingleton(e.e).with_type(TBag(e.e.type)))))
    def visit(self, e, *args):
        if isinstance(e, Exp) and _sametype(e, self.needle) and self.pool == self.needle_pool and alpha_equivalent(self.needle, e) and self.needle_context.alpha_equivalent(self.ctx):
            return self.ctx.adapt(self.replacement, self.needle_context)
        return super().visit(e, *args)

def replace(
        haystack : Exp, haystack_context : Context, haystack_pool : Pool,
        needle : Exp, needle_context : Context, needle_pool : Pool,
        replacement : Exp) -> Exp:
    """Replace an expression `needle` with `replacement` in `haystack`.

    Other parameters:
        haystack_context - the context describing the haystack
        haystack_pool - the pool for the haystack
        needle_context - the context describing the needle and replacement
        needle_pool - the pool for the needle and replacement

    This function is much smarter and safer than other expression replacement
    strategies: if `needle` and `replacement` are two different expressions
    that compute the same output, then the returned expression will compute the
    same output as `haystack`.

    Suppose we want to replace `x` with 0 in

        Map {x -> x + 1} (xs + [x]).

    Did we mean to replace the bound `x`, or the top-level `x`?  This function
    resolves the ambiguity by requiring a description of the context for `x`.

    This function also does smart variable renaming.  For instance, suppose
    we want to replace `x` with `x+1` in the context where `x in xs`.  Given
    the haystack

        Map {y -> y + 1} xs

    this function will realize that `y` and `x` are alpha equivalent and produce

        Map {y -> (y+1) + 1} xs.
    """
    return _Replacer(haystack_context, haystack_pool, needle, needle_context, needle_pool, replacement).visit(haystack)

def more_specific_context(ctx1 : Context, ctx2 : Context) -> Context:
    """Return the one of ctx1 or ctx2 that is legal for more expressions.

    This function raises ValueError if the contexts cannot be reconciled.
    """
    a = ctx1
    while a != ctx2:
        a = a.parent()
    if a == ctx2:
        return ctx1
    a = ctx2
    while a != ctx1:
        a = a.parent()
    if a == ctx1:
        return ctx2
    raise ValueError("no context in common: {}, {}".format(ctx1, ctx2))
