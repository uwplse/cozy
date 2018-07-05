## TODO: I don't understand "argument" below.  An argument is an expression
## but not necessarily a variable.  Do you mean a formal parameter?  But it
## isn't provided as an argument.  Please explain.
## TODO: A context describes variables and functions, but this comment only
## gives more information about variables.  What are the types of
## functions?  Are all functions treated uniformly with variables (there
## are the same types of functions as variables), or something else?
## TODO: What is the reason for the name "shred"?  Can you come up with a
## more informative name?
## TODO: From the documentation, it wasn't clear whether shred returns a
## heterogeneous list of expressions and contexts, or a list of pairs.
## Actually, shred returns a list of triples.  The last element is a pool
## (I'm not yet sure what that is.) Please update the documentation, here
## and at the definition of shred.
## TODO: Is replace context-aware in that it does alpha-renaming?  Please
## clarify "context-aware".

"""Classes for managing "contexts".

A Context object describes in-scope variables and functions.  Each variable is
one of
 - a state variable (part of the data structure state)
 - an argument (provided as an argument to a method call)
 - a binder (a bound variable introduced in a lambda)

Important functions:
 - shred: enumerate subexpressions and contexts from a top-level expression
 - replace: context-aware expression replacement
"""

from collections import OrderedDict
import itertools

from cozy.common import OrderedSet, unique, Visitor
from cozy.syntax import TFunc, TBag, Exp, EVar, EAll, ESingleton
from cozy.target_syntax import EDeepIn
from cozy.evaluation import eval
from cozy.syntax_tools import pprint, alpha_equivalent, free_vars, subst, BottomUpRewriter
from cozy.pools import Pool, RUNTIME_POOL, STATE_POOL

## TODO: Document each method.
class Context(object):
    def vars(self) -> {(EVar, Pool)}:
        raise NotImplementedError()
    def funcs(self) -> {str:TFunc}:
        raise NotImplementedError()
    def parent(self):
        raise NotImplementedError()
    def complexity(self):
        n = 0
        ctx = self
        while ctx is not None:
            n += 1
            ctx = ctx.parent()
        return n
    def legal_for(self, fvs : {EVar}) -> bool:
        vs = {v for (v, pool) in self.vars()}
        return all(v in vs for v in fvs)
    def instantiate_examples(self, examples : [dict]) -> [dict]:
        raise NotImplementedError()
    def alpha_equivalent(self, other) -> bool:
        raise NotImplementedError()
    def adapt(self, e : Exp, ctx) -> Exp:
        raise NotImplementedError()
    def path_conditions(self) -> [Exp]:
        raise NotImplementedError()
    def path_condition(self):
        return EAll(self.path_conditions())
    def generalize(self, fvs):
        raise NotImplementedError()

## TODO: document the fields (the constructor arguments), and state the
## contract (exactly one of state_vars and args is non-None).
class RootCtx(Context):
    def __init__(self, state_vars : [Exp], args : [Exp], funcs : {str:TFunc} = None):
        self.state_vars = OrderedSet(state_vars)
        self.args = OrderedSet(args)
        self.functions = OrderedDict(funcs or ())
        assert not (self.state_vars & self.args)
    def vars(self):
        ## Since exactly one of state_vars and args is non-None, I think an
        ## "if" would be clearer than `chain`.
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
    def adapt(self, e : Exp, ctx) -> Exp:
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
        assert v.type == bag.type.t
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
    def adapt(self, e : Exp, ctx) -> Exp:
        if self == ctx:
            return e
        if self.alpha_equivalent(ctx):
            e = self._parent.adapt(e, ctx._parent)
            return subst(e, { ctx.var.id : self.var })
        return self._parent.adapt(e, ctx)
    def path_conditions(self):
        pcs = [pc for pc in self._parent.path_conditions() if self.var not in free_vars(pc)]
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
        return "UnderBinder(parent={}, v={}, bag={}, bag_pool={})".format(self._parent, self.var, self.bag, self.pool)
    def __str__(self):
        return "{} in {}, {}".format(self.var.id, pprint(self.bag), self._parent)

class _Shredder(Visitor):
    def __init__(self, ctx, pool=RUNTIME_POOL):
        self.root_ctx = ctx
        self.ctx = ctx
        self.pool = pool
    def visit_ELambda(self, e, bag):
        ## It's inconsistent that visit_EStateVar uses a code pattern of
        ## saving the old value and reinstating it, whereas this method
        ## recomputes the value.  I think it would be more consistent to
        ## use the old_* pattern consistently.  Even though it will take
        ## one more line of code, it conveys the intention more clearly.
        ## The same comment applies to _Replacer.
        self.ctx = UnderBinder(self.ctx, e.arg, bag, self.pool)
        yield from self.visit(e.body)
        self.ctx = self.ctx.parent()
    def visit_EStateVar(self, e):
        yield (e, self.ctx, self.pool)
        old_pool = self.pool
        old_ctx = self.ctx
        self.pool = STATE_POOL
        self.ctx = self.root_ctx
        yield from self.visit(e.e)
        self.pool = old_pool
        self.ctx = old_ctx
    def visit_EMap(self, e):
        yield (e, self.ctx, self.pool)
        yield from self.visit(e.e)
        yield from self.visit(e.f, e.e)
    def visit_EFilter(self, e):
        yield (e, self.ctx, self.pool)
        yield from self.visit(e.e)
        yield from self.visit(e.p, e.e)
    def visit_EFlatMap(self, e):
        yield (e, self.ctx, self.pool)
        yield from self.visit(e.e)
        yield from self.visit(e.f, e.e)
    def visit_EArgMin(self, e):
        yield (e, self.ctx, self.pool)
        yield from self.visit(e.e)
        yield from self.visit(e.f, e.e)
    def visit_EArgMax(self, e):
        yield (e, self.ctx, self.pool)
        yield from self.visit(e.e)
        yield from self.visit(e.f, e.e)
    def visit_EMakeMap2(self, e):
        yield (e, self.ctx, self.pool)
        yield from self.visit(e.e)
        yield from self.visit(e.value, e.e)
    def visit_EMakeMinHeap(self, e):
        yield (e, self.ctx, self.pool)
        yield from self.visit(e.e)
        yield from self.visit(e.f, e.e)
    def visit_EMakeMaxHeap(self, e):
        yield (e, self.ctx, self.pool)
        yield from self.visit(e.e)
        yield from self.visit(e.f, e.e)
    def visit_ELet(self, e):
        yield (e, self.ctx, self.pool)
        yield from self.visit(e.e)
        yield from self.visit(e.f, ESingleton(e.e).with_type(TBag(e.e.type)))
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

def shred(e : Exp, context : Context, pool : Pool = RUNTIME_POOL) -> [(Exp, Context, Pool)]:
    return _Shredder(context, pool).visit(e)

def _sametype(e1 : Exp, e2 : Exp):
    if hasattr(e1, "type") and hasattr(e2, "type"):
        return e1.type == e2.type
    return True

class _Replacer(BottomUpRewriter):
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
        self.ctx = UnderBinder(self.ctx, e.arg, bag, self.pool)
        new_body = self.visit(e.body)
        self.ctx = self.ctx.parent()
        return self.join(e, (e.arg, new_body))
    def visit_EStateVar(self, e):
        old_pool = self.pool
        old_ctx = self.ctx
        self.pool = STATE_POOL
        self.ctx = self.root_ctx
        ee = self.visit(e.e)
        self.pool = old_pool
        self.ctx = old_ctx
        return self.join(e, (ee,))
    def visit_EMap(self, e):
        return self.join(e, (self.visit(e.e), self.visit(e.f, e.e)))
    def visit_EFilter(self, e):
        return self.join(e, (self.visit(e.e), self.visit(e.p, e.e)))
    def visit_EFlatMap(self, e):
        return self.join(e, (self.visit(e.e), self.visit(e.f, e.e)))
    def visit_EArgMin(self, e):
        return self.join(e, (self.visit(e.e), self.visit(e.f, e.e)))
    def visit_EArgMax(self, e):
        return self.join(e, (self.visit(e.e), self.visit(e.f, e.e)))
    def visit_EMakeMap2(self, e):
        return self.join(e, (self.visit(e.e), self.visit(e.value, e.e)))
    def visit_EMakeMinHeap(self, e):
        return self.join(e, (self.visit(e.e), self.visit(e.f, e.e)))
    def visit_EMakeMaxHeap(self, e):
        return self.join(e, (self.visit(e.e), self.visit(e.f, e.e)))
    def visit_ELet(self, e):
        return self.join(e, (self.visit(e.e), self.visit(e.f, ESingleton(e.e).with_type(TBag(e.e.type)))))
    def visit(self, e, *args):
        if isinstance(e, Exp) and _sametype(e, self.needle) and self.pool == self.needle_pool and alpha_equivalent(self.needle, e) and self.needle_context.alpha_equivalent(self.ctx):
            return self.ctx.adapt(self.replacement, self.needle_context)
        return super().visit(e, *args)

def replace(
        haystack : Exp, haystack_context : Context, haystack_pool : Pool,
        needle : Exp, needle_context : Context, needle_pool : Pool,
        replacement : Exp) -> Exp:
    return _Replacer(haystack_context, haystack_pool, needle, needle_context, needle_pool, replacement).visit(haystack)
