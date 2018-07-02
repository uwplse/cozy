"""Utilities for working with syntax trees.

Important functions:
 - pprint: prettyprint a syntax tree
 - free_vars: compute the set of free variables
 - alpha_equivalent: test alpha equivalence of two expressions
 - tease_apart: separate a packed expression into its state and runtime
    components
"""

import collections
from contextlib import contextmanager
import sys
import itertools
import json
import functools
from enum import Enum

from cozy import common
from cozy import syntax
from cozy import target_syntax
from cozy import pools

def var_name(v):
    if isinstance(v, str):
        return v
    if isinstance(v, syntax.EVar):
        return v.id
    raise TypeError(v)

def fresh_var(type, hint="var", omit=None):
    if omit is not None:
        omit = { var_name(v) for v in omit }
    return syntax.EVar(common.fresh_name(hint, omit=omit)).with_type(type)

def mk_lambda(t, l):
    v = fresh_var(t)
    return target_syntax.ELambda(v, l(v))

def compose(f1 : target_syntax.ELambda, f2 : target_syntax.ELambda) -> target_syntax.ELambda:
    return mk_lambda(f2.arg.type, lambda v: f1.apply_to(f2.apply_to(v)))

class BottomUpExplorer(common.Visitor):
    def visit_ADT(self, x):
        new_children = tuple(self.visit(child) for child in x.children())
        return self.join(x, new_children)
    def visit_list(self, l):
        return self.join(l, tuple(self.visit(x) for x in l))
    def visit_tuple(self, l):
        return self.join(l, tuple(self.visit(x) for x in l))
    def visit_dict(self, d):
        return self.join(d, tuple((self.visit(k), self.visit(v)) for (k,v) in d.items()))
    def visit_object(self, o):
        return self.join(o, ())
    def join(self, x, new_children):
        pass

class BottomUpRewriter(BottomUpExplorer):
    def join(self, x, new_children):
        if isinstance(x, common.ADT):
            if all(a is b for (a, b) in zip(x.children(), new_children)):
                return x
            out = type(x)(*new_children)
            if isinstance(x, syntax.Exp) and hasattr(x, "type"):
                out.type = x.type
            return out
        elif type(x) in [list, tuple, dict]:
            if type(x) in [list, tuple] and all(a is b for (a, b) in zip(x, new_children)):
                return x
            return type(x)(new_children)
        else:
            return x

class PathAwareExplorer(BottomUpExplorer):
    """
    A bottom-up explorer that maintains and presents an integer tuple path to
    each visit_Foo invocation.
    """
    def visit_ADT(self, x, path, *args, **kwargs):
        new_children = tuple(
            self.visit(child, path + (i,), *args, **kwargs)
            for i, child in enumerate(x.children()))
        return self.join(x, new_children)
    def visit_list(self, l, path, *args, **kwargs):
        return self.join(l, tuple(self.visit(x, path + (i,), *args, **kwargs)
            for i, x in enumerate(l)))
    def visit_tuple(self, l, path, *args, **kwargs):
        return self.join(l, tuple(self.visit(x, path + (i,), *args, **kwargs)
            for i, x in enumerate(l)))
    def visit_dict(self, d, path, *args, **kwargs):
        return self.join(d, tuple(
            (self.visit(k, path + (i * 2,), *args, **kwargs),
             self.visit(v, path + (i * 2 + 1,), *args, **kwargs))
            for i, (k, v) in enumerate(d.items())))
    def visit_object(self, o, path, *args, **kwargs):
        return self.join(o, ())

class PathedTreeDumper(PathAwareExplorer):
    """
    Prints an expression tree with the path tuple before each node.
    """
    @classmethod
    def dump(cls, s):
        return cls().visit(s, ())

    def visit_Exp(self, e, path):
        print("{} -> {}".format(path, pprint(e)))
        for i, c in enumerate(e.children()):
            self.visit(c, path + (i,))

    visit_Stm = visit_Exp

class PathAwareRewriter(PathAwareExplorer, BottomUpRewriter):
    pass

def strip_EStateVar(e : syntax.Exp):
    class V(BottomUpRewriter):
        def visit_EStateVar(self, e):
            return self.visit(e.e)
    return V().visit(e)

class DeepCopier(BottomUpRewriter):
    def join(self, x, new_children):
        if isinstance(x, common.ADT):
            out = type(x)(*new_children)
            if isinstance(x, syntax.Exp) and hasattr(x, "type"):
                out.type = x.type
            return out
        elif type(x) in [list, tuple, dict]:
            return type(x)(new_children)
        else:
            return x

_DEEP_COPIER = DeepCopier()

def deep_copy(ast):
    return _DEEP_COPIER.visit(ast)

def shallow_copy(ast):
    return _DEEP_COPIER.join(ast, ast.children())

def all_types(ast):
    class TypeCollector(BottomUpExplorer):
        def visit_Type(self, t):
            yield from super().visit_ADT(t)
            yield t
        def visit_Exp(self, e):
            yield from super().visit_ADT(e)
            t = getattr(e, "type", None)
            if t is not None:
                yield from self.visit(t)
        def visit_object(self, o):
            return ()
        def join(self, t, children):
            return itertools.chain(*children)
    return common.unique(TypeCollector().visit(ast))

class PrettyPrinter(common.Visitor):
    def __init__(self):
        # settings
        self.format = "plain" # or "html"

    def format_keyword(self, kw):
        if self.format == "html":
            return '<span class="kw">{}</span>'.format(kw)
        return kw

    def format_builtin(self, builtin):
        if self.format == "html":
            return '<span class="builtin">{}</span>'.format(builtin)
        return builtin

    def format_lt(self):
        return "&lt;" if self.format == "html" else "<"

    def format_gt(self):
        return "&gt;" if self.format == "html" else ">"

    def format_comment(self, comment):
        return '<span class="comment">{}</span>'.format(comment) if self.format == "html" else comment

    def visit_Spec(self, spec):
        s = spec.name + ":\n"
        for name, t in spec.types:
            s += "  {} {} = {}\n".format(self.format_keyword("type"), name, self.visit(t))
        for name, t in spec.statevars:
            s += "  {} {} : {}\n".format(self.format_keyword("state"), name, self.visit(t))
        for e in spec.assumptions:
            s += "  {} {};\n".format(self.format_keyword("assume"), self.visit(e))
        for op in spec.methods:
            s += str(self.visit(op))
        return s

    def visit_TEnum(self, enum):
        return "{} {{ {} }}".format(self.format_keyword("enum"), ", ".join(enum.cases))

    def visit_TNamed(self, named):
        return named.id

    def visit_TNative(self, t):
        return t.name

    def visit_TApp(self, app):
        return "{}{lt}{}{gt}".format(app.t, self.visit(app.args), lt=self.format_lt(), gt=self.format_gt())

    def visit_TBag(self, s):
        return "Bag{lt}{}{gt}".format(self.visit(s.t), lt=self.format_lt(), gt=self.format_gt())

    def visit_TSet(self, s):
        return "Set{lt}{}{gt}".format(self.visit(s.t), lt=self.format_lt(), gt=self.format_gt())

    def visit_TList(self, s):
        return "List{lt}{}{gt}".format(self.visit(s.t), lt=self.format_lt(), gt=self.format_gt())

    def visit_TMap(self, m):
        return "Map{lt}{}, {}{gt}".format(self.visit(m.k), self.visit(m.v), lt=self.format_lt(), gt=self.format_gt())

    def visit_THeap(self, h):
        return "Heap{lt}{}{gt}".format(self.visit(h.t), lt=self.format_lt(), gt=self.format_gt())

    def visit_TIntrusiveLinkedList(self, h):
        return "IntrusiveLinkedList{lt}{}{gt}".format(self.visit(h.t), lt=self.format_lt(), gt=self.format_gt())

    def visit_TNativeSet(self, h):
        return "NativeSet{lt}{}{gt}".format(self.visit(h.t), lt=self.format_lt(), gt=self.format_gt())

    def visit_TNativeList(self, h):
        return "NativeList{lt}{}{gt}".format(self.visit(h.t), lt=self.format_lt(), gt=self.format_gt())

    def visit_THashMap(self, h):
        return "HashMap{lt}{}, {}{gt}".format(self.visit(h.k), self.visit(h.v), lt=self.format_lt(), gt=self.format_gt())

    def visit_TInt(self, t):
        return "Int"

    def visit_TLong(self, t):
        return "Long"

    def visit_TFloat(self, t):
        return "Float"

    def visit_TBool(self, t):
        return "Bool"

    def visit_TString(self, t):
        return "String"

    def visit_TTuple(self, t):
        return "({})".format(", ".join(self.visit(tt) for tt in t.ts))

    def visit_TRecord(self, r):
        return "{{ {} }}".format(", ".join("{} : {}".format(f, self.visit(t)) for f, t in r.fields))

    def visit_THandle(self, t):
        return t.statevar

    def visit_ConcreteType(self, t):
        return t.prettyprint()

    def visit_Query(self, q):
        s = "\n"
        if q.docstring:
            s += "  {}\n".format(self.format_comment("/** {} */".format(q.docstring)))
        s += "  {} {}({}):\n".format(self.format_keyword("query"), q.name, ", ".join("{} : {}".format(name, self.visit(t)) for name, t in q.args))
        for e in q.assumptions:
            s += "    {} {};\n".format(self.format_keyword("assume"), self.visit(e))
        s += "    {}\n".format(self.visit(q.ret))
        return s

    def visit_Op(self, q):
        s = "\n"
        s += "  {} {}({}):\n".format(self.format_keyword("op"), q.name, ", ".join("{} : {}".format(name, self.visit(t)) for name, t in q.args))
        for e in q.assumptions:
            s += "    {} {};\n".format(self.format_keyword("assume"), self.visit(e))
        s += "{}\n".format(self.visit(q.body, "    "))
        return s

    def visit_EVar(self, e):
        return e.id

    def visit_EBool(self, e):
        return self.format_builtin("true" if e.val else "false")

    def visit_EStr(self, e):
        return json.dumps(e.val)

    def visit_ENum(self, e):
        return str(e.val)

    def visit_EEnumEntry(self, e):
        return e.name

    def visit_ENull(self, e):
        return self.format_builtin("null")

    def visit_ELambda(self, e):
        return "{} -> {}".format(e.arg.id, self.visit(e.body))

    def visit_EMapGet(self, e):
        return "{}[{}]".format(self.visit(e.map), self.visit(e.key))

    def visit_EListGet(self, e):
        return "{}[{}]".format(self.visit(e.e), self.visit(e.index))

    def visit_EListSlice(self, e):
        return "{}[{}:{}]".format(self.visit(e.e), self.visit(e.start), self.visit(e.end))

    def visit_EMap(self, e):
        return "{} {{{}}} ({})".format(self.format_builtin("Map"), self.visit(e.f), self.visit(e.e))

    def visit_EFilter(self, e):
        return "{} {{{}}} ({})".format(self.format_builtin("Filter"), self.visit(e.p), self.visit(e.e))

    def visit_EFlatMap(self, e):
        return "{} {{{}}} ({})".format(self.format_builtin("FlatMap"), self.visit(e.f), self.visit(e.e))

    def visit_EBinOp(self, e):
        op = e.op.replace("<", self.format_lt()).replace(">", self.format_gt())
        return "({} {} {})".format(self.visit(e.e1), op, self.visit(e.e2))

    def visit_ECond(self, e):
        return "({} ? {} : {})".format(self.visit(e.cond), self.visit(e.then_branch), self.visit(e.else_branch))

    def visit_EUnaryOp(self, e):
        return "({} {})".format(e.op, self.visit(e.e))

    def visit_EArgMin(self, e):
        if e.f.body == e.f.arg:
            return "{} {}".format(self.format_builtin("min"), self.visit(e.e))
        else:
            return "{} {{{}}} {}".format(self.format_builtin("argmin"), self.visit(e.f), self.visit(e.e))

    def visit_EArgMax(self, e):
        if e.f.body == e.f.arg:
            return "{} {}".format(self.format_builtin("max"), self.visit(e.e))
        else:
            return "{} {{{}}} {}".format(self.format_builtin("argmax"), self.visit(e.f), self.visit(e.e))

    def visit_EGetField(self, e):
        return "({}).{}".format(self.visit(e.e), e.f)

    def visit_EMakeRecord(self, e):
        return "{{ {} }}".format(", ".join("{} : {}".format(name, self.visit(val)) for name, val in e.fields))

    def visit_EEmptyList(self, e):
        return "[]"

    def visit_ESingleton(self, e):
        return "[{}]".format(self.visit(e.e))

    def visit_EListComprehension(self, e):
        return "[{} | {}]".format(self.visit(e.e), ", ".join(self.visit(clause) for clause in e.clauses))

    def visit_EAlloc(self, e):
        return "{} {}({})".format(self.format_keyword("new"), self.visit(e.t), ", ".join(self.visit(arg) for arg in e.args))

    def visit_ECall(self, e):
        return "{}({})".format(e.func, ", ".join(self.visit(arg) for arg in e.args))

    def visit_ETuple(self, e):
        return "({})".format(", ".join(self.visit(e) for e in e.es))

    def visit_ETupleGet(self, e):
        return "({}).{}".format(self.visit(e.e), e.n)

    def visit_ELet(self, e):
        return "{} {} = {} in {}".format(self.format_keyword("let"), e.f.arg.id, self.visit(e.e), self.visit(e.f.body))

    def visit_CPull(self, c):
        return "{} {lt}- {}".format(c.id, self.visit(c.e), lt=self.format_lt())

    def visit_CCond(self, c):
        return self.visit(c.e)

    def visit_ADT(self, e, *args, **kwargs):
        return "{}({})".format(type(e).__name__, ", ".join(self.visit(x) for x in e.children()))

    def visit_object(self, e, *args, **kwargs):
        print("Warning: implement prettyprinting for {}".format(type(e).__name__), file=sys.stderr)
        return repr(e)

    def visit_SNoOp(self, s, indent=""):
        return "{}{};".format(indent, self.format_keyword("pass"))

    def visit_SCall(self, s, indent=""):
        return "{}{}.{}({});".format(indent, self.visit(s.target), s.func, ", ".join(self.visit(arg) for arg in s.args))

    def visit_SAssign(self, s, indent=""):
        return "{}{} = {};".format(indent, self.visit(s.lhs), self.visit(s.rhs))

    def visit_SDecl(self, s, indent=""):
        return "{}{} {} = {};".format(indent, self.format_keyword("let"), s.id, self.visit(s.val))

    def visit_SSeq(self, s, indent=""):
        return "{}\n{}".format(self.visit(s.s1, indent), self.visit(s.s2, indent))

    def visit_SMapUpdate(self, s, indent=""):
        return "{indent}{} {} {} {}:\n{}".format(
            self.format_keyword("with"),
            self.visit(target_syntax.EMapGet(s.map, s.key)),
            self.format_keyword("as"),
            s.val_var.id,
            self.visit(s.change, indent + "  "),
            indent=indent)

    def visit_SMapPut(self, s, indent=""):
        return "{indent}{} = {};".format(
            self.visit(target_syntax.EMapGet(s.map, s.key)),
            self.visit(s.value),
            indent=indent)

    def visit_SMapDel(self, s, indent=""):
        return "{indent}{} {};".format(
            self.format_keyword("del"),
            self.visit(target_syntax.EMapGet(s.map, s.key)),
            indent=indent)

    def visit_SForEach(self, s, indent=""):
        return "{}{For} {} {In} {}:\n{}".format(
            indent,
            s.id.id,
            self.visit(s.iter),
            self.visit(s.body, indent + "  "),
            For=self.format_keyword("for"),
            In=self.format_keyword("in"))

    def visit_SIf(self, s, indent=""):
        if isinstance(s.else_branch, syntax.SNoOp):
            return "{indent}{If} {} {{\n{}\n{indent}}}".format(self.visit(s.cond), self.visit(s.then_branch, indent + "  "), indent=indent, If=self.format_keyword("if"))
        return "{indent}{If} {} {{\n{}\n{indent}}} {Else} {{\n{}\n{indent}}}".format(
            self.visit(s.cond),
            self.visit(s.then_branch, indent + "  "),
            self.visit(s.else_branch, indent + "  "),
            indent=indent,
            If=self.format_keyword("if"),
            Else=self.format_keyword("else"))

_PRETTYPRINTER = PrettyPrinter()
def pprint(ast, format="plain"):
    _PRETTYPRINTER.format = format
    return _PRETTYPRINTER.visit(ast)

def free_funcs(e : syntax.Exp) -> { str : syntax.TFunc }:
    res = collections.OrderedDict()
    for x in all_exps(e):
        if isinstance(x, syntax.ECall):
            t = syntax.TFunc(tuple(arg.type for arg in x.args), x.type)
            if x.func in res:
                assert res[x.func] == t
            else:
                res[x.func] = t
    return res

def free_vars(exp, counts=False):
    """Find all free variables in an AST.

    This function can be used on expressions, statements, and methods.

    If counts=False (the default), then this function returns an OrderedSet of
    EVar objects in a deterministic order.

    If counts=True, then this function returns an OrderedDict in a
    deterministic order mapping each EVar to the number of times it occurs in
    the AST.
    """

    res = collections.OrderedDict()
    bound = collections.defaultdict(int)

    scopes = [[]]

    def push_scope():
        scopes.append([])

    def bind(x):
        bound[x] += 1
        scopes[-1].append(x)

    class Bind(object):
        def __init__(self, var):
            self.var = var
        def exec(self):
            bind(self.var)

    class PopScope():
        def exec(self):
            scope = scopes.pop()
            for v in scope:
                bound[v] -= 1

    class PushScope():
        def exec(self):
            push_scope()

    # Find free variables using a work stack (to avoid running out of stack
    # frames on large expressions).  The work stack contains AST objects whose
    # free variables are yet to be added to `res`.  Additionally, it contains
    # Bind, PushScope, and PopScope objects indicating when scopes start and
    # end and where bound variable are introduced.
    stk = [exp]
    while stk:
        x = stk.pop()
        if isinstance(x, PushScope) or isinstance(x, PopScope) or isinstance(x, Bind):
            x.exec()
        elif isinstance(x, syntax.EVar):
            if not bound[x]:
                res[x] = res.get(x, 0) + 1
        elif isinstance(x, target_syntax.EStateVar):
            subres = free_vars(x.e, counts=True)
            for k, v in subres.items():
                res[k] = res.get(k, 0) + v
        elif isinstance(x, target_syntax.ELambda):
            push_scope()
            bind(x.arg)
            stk.append(PopScope())
            stk.append(x.body)
        elif isinstance(x, syntax.EListComprehension):
            raise NotImplementedError()
        elif isinstance(x, syntax.Method):
            push_scope()
            args = [syntax.EVar(a).with_type(t) for (a, t) in x.args]
            for a in args:
                bind(a)
            stk.append(PopScope())
            if isinstance(x, syntax.Query):
                stk.extend(reversed(x.assumptions))
                stk.append(x.ret)
            elif isinstance(x, syntax.Op):
                stk.extend(reversed(x.assumptions))
                stk.append(x.body)
            else:
                raise NotImplementedError()
        elif isinstance(x, syntax.SDecl):
            v = syntax.EVar(x.id)
            if hasattr(x.val, "type"):
                v = v.with_type(x.val.type)
            stk.append(Bind(v))
            stk.append(x.val)
        elif isinstance(x, syntax.SIf):
            for branch in (x.then_branch, x.else_branch):
                stk.append(PopScope())
                stk.append(branch)
                stk.append(PushScope())
            stk.append(x.cond)
        elif isinstance(x, syntax.SForEach):
            stk.append(PopScope())
            stk.append(x.body)
            stk.append(Bind(x.id))
            stk.append(PushScope())
            stk.append(x.iter)
        elif isinstance(x, target_syntax.SWhile):
            stk.append(PopScope())
            stk.append(x.body)
            stk.append(PushScope())
            stk.append(x.e)
        elif isinstance(x, target_syntax.SEscapableBlock):
            push_scope()
            stk.append(PopScope())
            stk.append(x.body)
        elif isinstance(x, target_syntax.SMapUpdate):
            stk.append(PopScope())
            stk.append(x.change)
            stk.append(Bind(x.val_var))
            stk.append(PushScope())
            stk.append(x.key)
            stk.append(x.map)
        elif isinstance(x, common.ADT):
            stk.extend(reversed(x.children()))
        elif isinstance(x, list) or isinstance(x, tuple):
            stk.extend(reversed(x))
        elif isinstance(x, (str, int, float)):
            continue
        else:
            raise NotImplementedError(repr(x))

    if not counts:
        res = common.OrderedSet(res.keys())
    return res

def all_exps(x):
    q = [x]
    while q:
        e = q.pop()
        if isinstance(e, tuple) or isinstance(e, list):
            q.extend(e)
            continue
        if isinstance(e, syntax.Exp):
            yield e
        if isinstance(e, common.ADT):
            q.extend(e.children())

Unknown = collections.namedtuple("Unknown", [])
ElemOf = collections.namedtuple("ElemOf", ["bag"])
Exactly = collections.namedtuple("Exactly", ["e"])
Context = collections.namedtuple("Context", [
    "toplevel",
    "e",
    "facts",
    "replace_e_with",
    "bound_vars",
    "var_sources",
    "pool"])

class FragmentEnumerator(common.Visitor):
    # This visitor's methods use a weird pattern:
    #     yield (lambda r: ...)(r)
    # This is because lambdas are capture-by-reference in Python! Since r is
    # overwritten at each loop iteration, that's a problem. Defining a fresh
    # function and immediately calling it is a simple way to force
    # capture-by-value for r instead.
    def __init__(self, toplevel, pool=pools.RUNTIME_POOL):
        self.toplevel = toplevel
        self.bound_vars = []
        self.assumptions = []
        self.pool_stack = [pool]

    def currently_bound(self) -> {syntax.EVar}:
        return common.OrderedSet(v for v, src in self.bound_vars)

    def current_assumptions(self) -> [syntax.Exp]:
        return list(self.assumptions)

    @contextmanager
    def intro_vars(self, vs):
        vs = common.make_random_access(vs)
        for v, src in vs:
            assert isinstance(v, syntax.EVar)
            assert isinstance(src, ElemOf) or isinstance(src, Exactly) or isinstance(src, Unknown)
        self.bound_vars.extend(vs)
        with common.save_property(self, "assumptions"):
            for v, src in vs:
                self.assumptions = [a for a in self.assumptions if v not in free_vars(a)]
            for v, src in vs:
                if isinstance(src, ElemOf):
                    if v not in free_vars(src.bag):
                        self.assumptions.append(target_syntax.EDeepIn(v, src.bag))
                elif isinstance(src, Exactly):
                    if v not in free_vars(src.e):
                        self.assumptions.append(syntax.EBinOp(v, "===", src.e).with_type(BOOL))
            yield
        for i in range(len(vs)):
            self.bound_vars.pop()

    @contextmanager
    def clear_bound(self):
        old_bound = self.bound_vars
        self.bound_vars = []
        yield
        self.bound_vars = old_bound

    @contextmanager
    @common.typechecked
    def push_assumptions(self, new_assumptions : [syntax.Exp] = []):
        self.assumptions.extend(new_assumptions)
        yield
        for i in range(len(new_assumptions)):
            self.assumptions.pop()

    def make_ctx(self, e):
        return Context(
            toplevel=self.toplevel,
            e=e,
            facts=self.current_assumptions(),
            replace_e_with=common.identity_func,
            bound_vars=self.currently_bound(),
            var_sources=common.OrderedDict(self.bound_vars),
            pool=self.pool_stack[-1])

    def update_repl(self, ctx, new_replace):
        return ctx._replace(replace_e_with=new_replace(ctx.replace_e_with))

    def visit_assumptions_seq(self, assumptions, i=0):
        if i >= len(assumptions):
            return
        for ctx in self.visit(assumptions[i]):
            yield self.update_repl(ctx, lambda r: lambda x: tuple(assumptions[:i]) + (x,) + tuple(assumptions[i:]))
        self.assumptions.append(assumptions[i])
        yield from self.visit_assumptions_seq(assumptions, i+1)

    def recurse_with_assumptions_about_bound_var(self, e : target_syntax.ELambda, src):
        yield self.make_ctx(e)
        with self.intro_vars([(e.arg, src)]):
            for ctx in self.visit(e.body):
                yield self.update_repl(ctx, lambda r: lambda x: target_syntax.ELambda(e.arg, r(x)))

    def visit_ELambda(self, obj):
        # The parent should tell us something about where the var comes from
        raise NotImplementedError(pprint(self.toplevel))

    def visit_EStateVar(self, e):
        """
        A very tricky case: the set of bound variables gets cleared for its
        children. Consider

            Filter {\v -> EStateVar(v)} C

        The `v` in the EStateVar is *different* from the `v` bound by the filter
        predicate, since this expression is conceptually equivalent to

            state s = v
            Filter {\v -> s} C
        """
        yield self.make_ctx(e)
        t = e.type
        self.pool_stack.append(pools.STATE_POOL)
        with self.clear_bound():
            for ctx in self.visit(e.e):
                yield self.update_repl(ctx, lambda r: lambda x: target_syntax.EStateVar(r(x)).with_type(t))
        self.pool_stack.pop()

    def visit_EFilter(self, e):
        yield self.make_ctx(e)
        t = e.type
        for ctx in self.visit(e.e):
            yield self.update_repl(ctx, lambda r: lambda x: target_syntax.EFilter(r(x), e.p).with_type(t))
        for ctx in self.recurse_with_assumptions_about_bound_var(e.p, ElemOf(e.e)):
            yield self.update_repl(ctx, lambda r: lambda x: target_syntax.EFilter(e.e, r(x)).with_type(t))

    def visit_EMap(self, e):
        yield self.make_ctx(e)
        t = e.type
        for ctx in self.visit(e.e):
            yield self.update_repl(ctx, lambda r: lambda x: target_syntax.EMap(r(x), e.f).with_type(t))
        for ctx in self.recurse_with_assumptions_about_bound_var(e.f, ElemOf(e.e)):
            yield self.update_repl(ctx, lambda r: lambda x: target_syntax.EMap(e.e, r(x)).with_type(t))

    def visit_EFlatMap(self, e):
        yield self.make_ctx(e)
        t = e.type
        for ctx in self.visit(e.e):
            yield self.update_repl(ctx, lambda r: lambda x: target_syntax.EFlatMap(r(x), e.f).with_type(t))
        for ctx in self.recurse_with_assumptions_about_bound_var(e.f, ElemOf(e.e)):
            yield self.update_repl(ctx, lambda r: lambda x: target_syntax.EFlatMap(e.e, r(x)).with_type(t))

    def visit_EMakeMap2(self, e):
        yield self.make_ctx(e)
        t = e.type
        for ctx in self.visit(e.e):
            yield self.update_repl(ctx, lambda r: lambda x: target_syntax.EMakeMap2(r(x), e.value).with_type(t))
        for ctx in self.recurse_with_assumptions_about_bound_var(e.value, ElemOf(e.e)):
            yield self.update_repl(ctx, lambda r: lambda x: target_syntax.EMakeMap2(e.e, r(x)).with_type(t))

    def visit_EArgMin(self, e):
        yield self.make_ctx(e)
        t = e.type
        for ctx in self.visit(e.e):
            yield self.update_repl(ctx, lambda r: lambda x: target_syntax.EArgMin(r(x), e.f).with_type(t))
        for ctx in self.recurse_with_assumptions_about_bound_var(e.f, ElemOf(e.e)):
            yield self.update_repl(ctx, lambda r: lambda x: target_syntax.EArgMin(e.e, r(x)).with_type(t))

    def visit_EArgMax(self, e):
        yield self.make_ctx(e)
        t = e.type
        for ctx in self.visit(e.e):
            yield self.update_repl(ctx, lambda r: lambda x: target_syntax.EArgMax(r(x), e.f).with_type(t))
        for ctx in self.recurse_with_assumptions_about_bound_var(e.f, ElemOf(e.e)):
            yield self.update_repl(ctx, lambda r: lambda x: target_syntax.EArgMax(e.e, r(x)).with_type(t))

    def visit_EMakeMinHeap(self, e):
        from cozy.structures.heaps import EMakeMinHeap
        yield self.make_ctx(e)
        t = e.type
        for ctx in self.visit(e.e):
            yield self.update_repl(ctx, lambda r: lambda x: EMakeMinHeap(r(x), e.f).with_type(t))
        for ctx in self.recurse_with_assumptions_about_bound_var(e.f, ElemOf(e.e)):
            yield self.update_repl(ctx, lambda r: lambda x: EMakeMinHeap(e.e, r(x)).with_type(t))

    def visit_EMakeMaxHeap(self, e):
        from cozy.structures.heaps import EMakeMaxHeap
        yield self.make_ctx(e)
        t = e.type
        for ctx in self.visit(e.e):
            yield self.update_repl(ctx, lambda r: lambda x: EMakeMaxHeap(r(x), e.f).with_type(t))
        for ctx in self.recurse_with_assumptions_about_bound_var(e.f, ElemOf(e.e)):
            yield self.update_repl(ctx, lambda r: lambda x: EMakeMaxHeap(e.e, r(x)).with_type(t))

    def visit_ELet(self, e):
        yield self.make_ctx(e)
        t = e.type
        for ctx in self.visit(e.e):
            yield self.update_repl(ctx, lambda r: lambda x: syntax.ELet(r(x), e.f).with_type(t))
        for ctx in self.recurse_with_assumptions_about_bound_var(e.f, Exactly(e.e)):
            yield self.update_repl(ctx, lambda r: lambda x: syntax.ELet(e.e, r(x)).with_type(t))

    def visit_ECond(self, e):
        yield self.make_ctx(e)
        for ctx in self.visit(e.cond):
            yield self.update_repl(ctx, lambda r: lambda x: syntax.ECond(r(x), e.then_branch, e.else_branch).with_type(e.type))
        with self.push_assumptions([e.cond]):
            for ctx in self.visit(e.then_branch):
                yield self.update_repl(ctx, lambda r: lambda x: syntax.ECond(e.cond, r(x), e.else_branch).with_type(e.type))
        with self.push_assumptions([syntax.ENot(e.cond)]):
            for ctx in self.visit(e.else_branch):
                yield self.update_repl(ctx, lambda r: lambda x: syntax.ECond(e.cond, e.then_branch, r(x)).with_type(e.type))

    def rebuild(self, obj, new_children):
        res = type(obj)(*new_children)
        if isinstance(obj, syntax.Exp):
            res = res.with_type(obj.type)
        return res

    def visit_Spec(self, s):
        yield self.make_ctx(s)
        with self.intro_vars([(syntax.EVar(v).with_type(t), Unknown()) for (v, t) in s.statevars]):
            with self.push_assumptions():
                for ctx in self.visit_assumptions_seq(s.assumptions):
                    yield self.update_repl(ctx, lambda r: lambda x: syntax.Spec(s.name, s.types, s.extern_funcs, s.statevars, r(x), s.methods, s.header, s.footer, s.docstring))
                for ctx in self.visit(s.methods):
                    yield self.update_repl(ctx, lambda r: lambda x: syntax.Spec(s.name, s.types, s.extern_funcs, s.statevars, s.assumptions, r(x), s.header, s.footer, s.docstring))

    def visit_Op(self, m):
        yield self.make_ctx(m)
        with self.intro_vars([(syntax.EVar(v).with_type(t), Unknown()) for (v, t) in m.args]):
            with self.push_assumptions():
                for ctx in self.visit_assumptions_seq(m.assumptions):
                    yield self.update_repl(ctx, lambda r: lambda x: syntax.Op(m.name, m.args, r(x), m.body, m.docstring))
                for ctx in self.visit(m.body):
                    yield self.update_repl(ctx, lambda r: lambda x: syntax.Op(m.name, m.args, m.assumptions, r(x), m.docstring))

    def visit_Query(self, q):
        yield self.make_ctx(q)
        with self.intro_vars([(syntax.EVar(v).with_type(t), Unknown()) for (v, t) in q.args]):
            with self.push_assumptions():
                for ctx in self.visit_assumptions_seq(q.assumptions):
                    yield self.update_repl(ctx, lambda r: lambda x: syntax.Query(q.name, q.visibility, q.args, r(x), q.ret, q.docstring))
                for ctx in self.visit(q.ret):
                    yield self.update_repl(ctx, lambda r: lambda x: syntax.Query(q.name, q.visibility, q.args, q.assumptions, r(x), q.docstring))

    def visit_ADT(self, obj):
        yield self.make_ctx(obj)
        children = obj.children()
        for i in range(len(children)):
            for ctx in self.visit(children[i]):
                yield self.update_repl(ctx, (lambda i: lambda r: lambda x: self.rebuild(obj, (children[:i] + (r(x),) + children[i+1:])))(i))

    def visit_list(self, l):
        return self.visit_tuple(tuple(l))

    def visit_tuple(self, t):
        yield self.make_ctx(t)
        for i in range(len(t)):
            for ctx in self.visit(t[i]):
                yield self.update_repl(ctx, (lambda i: lambda r: lambda x: t[:i] + (r(x),) + t[i+1:])(i))

    def visit_object(self, obj):
        yield self.make_ctx(obj)

    def visit(self, obj):
        yield from super().visit(obj)

def enumerate_fragments(e : syntax.Exp):
    """
    Yields Contexts ctx where
        ctx.e is a non-lambda subexpression of e
        ctx.facts are true assumptions whenever x is evaluated on any input to
            e (NOTE: these assumptions may be conservative, but they are never
            wrong)
        ctx.replace_e_with(x) == e (in general, r can be used to replace x with
            a new subexpr)
        ctx.bound_vars is the set of bound vars at x (i.e. in any potential
            replacement y, all free vars in y not in ctx will be free in r(y))

    Fragments are enumerated top-down (i.e. every expression comes before any
    of its subexpressions).
    """
    for ctx in FragmentEnumerator(e).visit(e):
        if isinstance(ctx.e, syntax.Exp) and not isinstance(ctx.e, syntax.ELambda):
            yield ctx

def replace(exp, old_exp, new_exp, safe=True, match=lambda e1, e2: e1 == e2):
    fvs = free_vars(old_exp) if safe else ()
    nfvs = free_vars(new_exp)
    class Replacer(BottomUpRewriter):
        def visit_ELambda(self, e):
            if e.arg in fvs:
                return e
            if e.arg in nfvs:
                new_arg = fresh_var(e.arg.type, omit=fvs|nfvs)
                e = target_syntax.ELambda(new_arg, subst(e.body, {e.arg.id:new_arg}))
            return target_syntax.ELambda(e.arg, self.visit(e.body))
        def visit(self, e):
            if isinstance(e, syntax.Exp) and match(e, old_exp):
                return new_exp
            return super().visit(e)
    return Replacer().visit(exp)

def rewrite_ret(q : syntax.Query, repl, keep_assumptions=True) -> syntax.Query:
    q = shallow_copy(q)
    q.ret = repl(q.ret)
    if not keep_assumptions:
        q.assumptions = ()
    return q

def subst_lval(lval, replacements):
    # Currently we only allow vars and lval.field as l-values.
    # Neither requires attention during substitution.
    return lval

@common.typechecked
def tease_apart(exp : syntax.Exp, avoid : {syntax.EVar} = set()) -> ([(syntax.EVar, syntax.Exp)], syntax.Exp):
    new_state = []
    omit = set(free_vars(exp) | avoid)

    class V(BottomUpRewriter):
        def visit_ELambda(self, e):
            omit.add(e.arg)
            return target_syntax.ELambda(e.arg, self.visit(e.body))
        def visit_EStateVar(self, e):
            e = e.e
            x = common.find_one(x for x in new_state if alpha_equivalent(x[1], e))
            if x is not None:
                return x[0]
            else:
                v = fresh_var(e.type, omit=omit)
                omit.add(v)
                new_state.append((v, e))
                return v

    new_exp = V().visit(exp)
    return (new_state, new_exp)

@common.typechecked
def purify(exp : syntax.Exp) -> syntax.Exp:
    st, exp = tease_apart(exp)
    for v, e in st:
        exp = target_syntax.ELet(e, target_syntax.ELambda(v, exp)).with_type(exp.type)
    return exp

def wrap_naked_statevars(e : syntax.Exp, state_vars : [syntax.EVar]):
    state_vars = common.OrderedSet(state_vars)
    class V(BottomUpRewriter):
        def visit_EVar(self, e):
            if e in state_vars:
                return target_syntax.EStateVar(e).with_type(e.type)
            return e
        def visit_EStateVar(self, e):
            return e
    return V().visit(e)

def subst(exp, replacements, tease=True):
    """
    Performs capture-avoiding substitution.
    Input:
        exp             - an Exp
        replacements    - {str:Exp} replacement map for variables
    Output:
        exp with each var mapped to its replacement (if any) from replacements
    """

    allfvs = set()
    for val in replacements.values():
        allfvs |= {fv.id for fv in free_vars(val)}

    if tease and any(isinstance(e, target_syntax.EStateVar) for e in all_exps(exp)):
        rvars = common.OrderedSet(syntax.EVar(v).with_type(e.type) for v, e in replacements.items())
        st, exp = tease_apart(exp, avoid=rvars)
        for i in range(len(st)):
            st[i] = (st[i][0], subst(st[i][1], replacements))
        exp = subst(exp, replacements, tease=False)
        return subst(exp, { v.id : target_syntax.EStateVar(e).with_type(e.type) for (v, e) in st }, tease=False)

    class Subst(common.Visitor):
        def visit_EVar(self, var):
            return replacements.get(var.id, var)
        def visit_EListComprehension(self, lcmp):
            return self.visit_lcmp(list(lcmp.clauses), 0, lcmp.e)
        def visit_lcmp(self, clauses, i, e):
            if i >= len(clauses):
                return syntax.EListComprehension(self.visit(e), tuple(clauses))
            c = clauses[i]
            if isinstance(c, syntax.CPull):
                if c.id in replacements:
                    raise NotImplementedError()
                if c.id in allfvs:
                    name = common.fresh_name()
                    r = { c.id : syntax.EVar(name) }
                    e = subst(e, r)
                    for j in range(i + 1, len(clauses)):
                        d = clauses[j]
                        if isinstance(d, syntax.CPull):
                            if any(v.id == d.id for r in replacements.values() for v in free_vars(r)):
                                raise NotImplementedError()
                            clauses[j] = syntax.CPull(d.id, subst(d.e, r))
                        elif isinstance(d, syntax.CCond):
                            clauses[j] = syntax.CCond(subst(d.e, r))
                else:
                    name = c.id
                clauses[i] = syntax.CPull(name, self.visit(c.e))
                return self.visit_lcmp(clauses, i + 1, e)
            elif isinstance(c, syntax.CCond):
                clauses[i] = syntax.CCond(self.visit(c.e))
                return self.visit_lcmp(clauses, i + 1, e)
        def visit_EStateVar(self, e):
            return target_syntax.EStateVar(subst(e.e, replacements))
        def visit_ELambda(self, e):
            m = replacements
            if e.arg.id in replacements:
                m = dict(m)
                del m[e.arg.id]
            arg = e.arg
            body = e.body
            while any(arg in free_vars(r) for r in replacements.values()):
                if hasattr(arg, "type"):
                    new_arg = fresh_var(arg.type)
                else:
                    new_arg = syntax.EVar(common.fresh_name())
                body = subst(body, { arg.id : new_arg })
                arg = new_arg
            return target_syntax.ELambda(arg, subst(body, m))
        def visit_ADT(self, e):
            children = e.children()
            children = tuple(self.visit(c) for c in children)
            return type(e)(*children)
        def visit_list(self, l):
            return [self.visit(x) for x in l]
        def visit_tuple(self, l):
            return tuple(self.visit(x) for x in l)
        def visit_dict(self, d):
            return {self.visit(k):self.visit(v) for (k,v) in d.items()}
        def visit_object(self, o):
            return o
        def visit_Type(self, t):
            return t
        def visit_Query(self, q):
            m = { name: repl for (name, repl) in replacements.items() if not any(n == name for (n, t) in q.args) }
            for (a, t) in q.args:
                for r in replacements.values():
                    if any(v.id == a for v in free_vars(r)):
                        raise NotImplementedError("need to rename query argument {} in {}".format(a, pprint(q)))
            return syntax.Query(
                q.name,
                q.visibility,
                q.args,
                [subst(a, m) for a in q.assumptions],
                subst(q.ret, m),
                q.docstring)
        def visit_Op(self, o):
            m = { name: repl for (name, repl) in replacements.items() if not any(n == name for (n, t) in o.args) }
            for (a, t) in o.args:
                for r in replacements.values():
                    if any(v.id == a for v in free_vars(r)):
                        raise NotImplementedError("need to rename op argument {} in {}".format(a, pprint(o)))
            return syntax.Op(
                o.name,
                o.args,
                [subst(a, m) for a in o.assumptions],
                subst(o.body, m),
                o.docstring)
        def visit_SAssign(self, s):
            return syntax.SAssign(
                subst_lval(s.lhs, replacements),
                self.visit(s.rhs))
        def visit_SCall(self, s):
            return syntax.SCall(
                subst_lval(s.target, replacements),
                s.func,
                self.visit(s.args))
        def visit(self, x, *args, **kwargs):
            res = super().visit(x, *args, **kwargs)
            if isinstance(res, syntax.Exp) and hasattr(x, "type") and not hasattr(res, "type"):
                res.type = x.type
            return res

    return Subst().visit(exp)

@common.typechecked
def qsubst(
        haystack : syntax.Exp,
        needle   : syntax.EVar,
        repl     : syntax.Exp):
    if repl.size() <= 1 or free_vars(haystack, counts=True).get(needle, 0) <= 1:
        return subst(haystack, { needle.id : repl })
    e = syntax.ELet(repl, target_syntax.ELambda(needle, haystack))
    if hasattr(haystack, "type"):
        e = e.with_type(haystack.type)
    return e

@common.typechecked
def alpha_equivalent(e1 : syntax.Exp, e2 : syntax.Exp) -> bool:
    """
    Equality on expression ASTs is syntactic equality; even variable names are
    compared. So,
        [x | x <- L] != [y | y <- L].
    However, alpha equivalence allows renaming of variables, so
        alpha_equivalent([x | x <- L], [y | y <- L]) == True.
    """
    class V(common.Visitor):
        def __init__(self):
            self.depth = 0
            self.remap_l = { } # maps e1 varnames ---> ids
            self.remap_r = { } # maps e2 varnames ---> ids

        @contextmanager
        @common.typechecked
        def unify(self, vs : [(syntax.EVar, syntax.EVar)], i : int = 0):
            if i >= len(vs):
                yield
            else:
                self.depth += 1
                v1, v2 = vs[i]
                with common.extend(self.remap_l, v1, self.depth):
                    with common.extend(self.remap_r, v2, self.depth):
                        with self.unify(vs, i + 1):
                            yield
                self.depth -= 1

        def visit_EVar(self, e1, e2):
            if not isinstance(e2, syntax.EVar):
                return False
            return self.remap_l.get(e1, e1) == self.remap_r.get(e2, e2)
        def visit_ELambda(self, e1, e2):
            if not isinstance(e2, target_syntax.ELambda):
                return False
            with self.unify([(e1.arg, e2.arg)]):
                return self.visit(e1.body, e2.body)
        def visit_EListComprehension(self, lcmp, other):
            if not isinstance(other, syntax.EListComprehension):
                return False
            if len(lcmp.clauses) != len(other.clauses):
                return False
            return self.visit_clauses(0, lcmp.clauses, other.clauses, lcmp.e, other.e)
        def visit_clauses(self, i, clauses1, clauses2, e1, e2):
            if i >= len(clauses1):
                return self.visit(e1, e2)
            c1 = clauses1[i]
            c2 = clauses2[i]
            if isinstance(c1, syntax.CPull):
                if not isinstance(c2, syntax.CPull):
                    return False
                with self.unify([(c1, c2)]):
                    return self.visit_clauses(i + 1, clauses1, clauses2, e1, e2)
            elif isinstance(c1, syntax.CCond):
                return self.visit(c1.e, c2.e) and self.visit_clauses(i + 1, clauses1, clauses2, e1, e2)
            else:
                raise NotImplementedError(pprint(c1))
        def visit_str(self, s1, s2):
            return s1 == s2
        def visit_int(self, i1, i2):
            return i1 == i2
        def visit_float(self, f1, f2):
            return f1 == f2
        def visit_tuple(self, t1, t2):
            return len(t1) == len(t2) and all(self.visit(x, y) for x, y in zip(t1, t2))
        def visit_list(self, t1, t2):
            return len(t1) == len(t2) and all(self.visit(x, y) for x, y in zip(t1, t2))
        def visit_Exp(self, e1, e2):
            if type(e1) is not type(e2):
                return False
            return all(self.visit(x, y) for (x, y) in zip(e1.children(), e2.children()))
        def visit_object(self, o, *args):
            raise NotImplementedError("{} ({})".format(type(o), repr(o)))

    return V().visit(e1, e2)

def freshen_binders(e : syntax.Exp, context):
    fvs = { v : True for v, p in context.vars() }
    class V(BottomUpRewriter):
        def __init__(self):
            self.rewrite = { }
        def visit_EVar(self, v):
            return self.rewrite.get(v, v)
        def visit_ELambda(self, l):
            if l.arg in fvs:
                new_arg = fresh_var(l.arg.type)
                # print("Rewriting: {} ----> {}".format(l.arg.id, new_arg.id))
                with common.extend(self.rewrite, l.arg, new_arg):
                    new_body = self.visit(l.body)
            else:
                new_arg = l.arg
                with common.extend(fvs, l.arg, True):
                    new_body = self.visit(l.body)
            return self.join(l, (new_arg, new_body))
    ee = V().visit(e)
    assert alpha_equivalent(e, ee)
    return ee

BOOL = syntax.TBool()

def implies(e1, e2):
    return syntax.EImplies(e1, e2)

def equal(e1, e2):
    return syntax.EEq(e1, e2)

@common.typechecked
def nnf(e : syntax.Exp, negate=False) -> syntax.Exp:
    """Convert a boolean expression to negation-normal-form (NNF)."""
    assert e.type == BOOL
    if isinstance(e, syntax.EUnaryOp) and e.op == "not":
        return nnf(e.e, negate=not negate)
    if isinstance(e, syntax.EBinOp) and e.op == "and":
        if negate:
            return syntax.EBinOp(nnf(e.e1, negate), "or", nnf(e.e2, negate)).with_type(BOOL)
        else:
            return syntax.EBinOp(nnf(e.e1), "and", nnf(e.e2)).with_type(BOOL)
    if isinstance(e, syntax.EBinOp) and e.op == "or":
        if negate:
            return syntax.EBinOp(nnf(e.e1, negate), "and", nnf(e.e2, negate)).with_type(BOOL)
        else:
            return syntax.EBinOp(nnf(e.e1), "or", nnf(e.e2)).with_type(BOOL)
    if isinstance(e, syntax.EBool):
        return syntax.EBool((not e.val) if negate else e.val).with_type(BOOL)
    if isinstance(e, syntax.EBinOp) and e.op == ">" and negate:
        return syntax.EBinOp(e.e1, "<=", e.e2).with_type(BOOL)
    if isinstance(e, syntax.EBinOp) and e.op == ">=" and negate:
        return syntax.EBinOp(e.e1, "<", e.e2).with_type(BOOL)
    if isinstance(e, syntax.EBinOp) and e.op == "<" and negate:
        return syntax.EBinOp(e.e1, ">=", e.e2).with_type(BOOL)
    if isinstance(e, syntax.EBinOp) and e.op == "<=" and negate:
        return syntax.EBinOp(e.e1, ">", e.e2).with_type(BOOL)
    return syntax.ENot(e) if negate else e

@common.typechecked
def dnf(e : syntax.Exp) -> [[syntax.Exp]]:
    """
    Convert a boolean expression to disjunction-normal-form (DNF). The input
    must already be in NNF.

    WARNING:
        This may result in an exponential blowup in the size of the expression.
    """
    assert e.type == BOOL
    if isinstance(e, syntax.EBinOp) and e.op == "or":
        return dnf(e.e1) + dnf(e.e2)
    if isinstance(e, syntax.EBinOp) and e.op == "and":
        cases1 = dnf(e.e1)
        cases2 = dnf(e.e2)
        return [c1 + c2 for c1 in cases1 for c2 in cases2]
    if isinstance(e, syntax.ECond):
        return dnf(syntax.EAny([
            syntax.EAll([            e.cond , e.then_branch]),
            syntax.EAll([syntax.ENot(e.cond), e.else_branch])]))
    return [[e]]

def break_binary(x, binary_children):
    stk = [x]
    while stk:
        x = stk.pop()
        children = binary_children(x)
        if children is None:
            yield x
        else:
            stk.extend(reversed(common.make_random_access(children)))

def break_ebinop(e : syntax.Exp, op : syntax.BOp):
    return break_binary(e, lambda e: (e.e1, e.e2) if isinstance(e, syntax.EBinOp) and e.op == op else None)

def break_conj(e : syntax.Exp):
    return break_ebinop(e, syntax.BOp.And)

def break_sum(e : syntax.Exp):
    return break_ebinop(e, "+")

def break_product(e : syntax.Exp):
    return break_ebinop(e, "*")

def break_seq(s : syntax.Stm):
    return break_binary(s, lambda s: (s.s1, s.s2) if isinstance(s, syntax.SSeq) else None)

def build_right_seq_stick(seq):
    """
    Builds a recursive SSeq where each elem is (node, following_seq).
    """
    stms = [s for s in break_seq(seq) if not isinstance(s, syntax.SNoOp)]

    if not stms:
        return syntax.SNoOp()

    reverse_iter = reversed(stms)
    head = next(reverse_iter)

    for s in reverse_iter:
        head = syntax.SSeq(s, head)

    return head

class Aeq(object):
    def __init__(self, e : syntax.Exp):
        self.e = e
    def __hash__(self):
        res = 0
        q = [self.e]
        while q:
            x = q[-1]
            del q[-1]
            if isinstance(x, syntax.EVar):
                continue
            elif isinstance(x, common.ADT):
                res *= 31
                res += hash(type(x))
                res %= 2**64
                q.extend(x.children())
            elif isinstance(x, tuple) or isinstance(x, list):
                q.extend(x)
            else:
                res += hash(x)
                # raise NotImplementedError(repr(x))
        return res % (2**64)
    def __eq__(self, other):
        return isinstance(other, Aeq) and alpha_equivalent(self.e, other.e)
    def __ne__(self, other):
        return not (self == other)

class ExpMap(object):
    def __init__(self, items=()):
        self.by_id = collections.OrderedDict()
        self.by_hash = collections.OrderedDict()
        for k, v in items:
            self[k] = v
    def _hash(self, k):
        return (type(k), k.type, k)
    def _unhash(self, h):
        return h[2]
    def get(self, k):
        i = id(k)
        try:
            return self.by_id[i]
        except KeyError:
            return self.by_hash.get(self._hash(k))
    def __setitem__(self, k, v):
        self.by_id[id(k)] = v
        self.by_hash[self._hash(k)] = v
    def __delitem__(self, k):
        i = id(k)
        if i in self.by_id:
            del self.by_id[i]
        del self.by_hash[self._hash(k)]
    def items(self):
        for (k, v) in self.by_hash.items():
            yield (self._unhash(k), v)
    def values(self):
        for k, v in self.items():
            yield v

_ReduceOp = collections.namedtuple("_ReduceOp", ("x", "n"))
_UnbindOp = collections.namedtuple("_UnbindOp", ("v",))

class IterativeReducer(object):
    def bind(self, v : syntax.EVar):
        pass

    def unbind(self, v : syntax.EVar):
        pass

    def visit(self, x):
        work_stack = [x]
        done_stack = []
        while work_stack:
            # print("TODO: {}; DONE: {}".format(work_stack, done_stack))
            top = work_stack.pop()
            if isinstance(top, _ReduceOp):
                args = [done_stack.pop() for i in range(top.n)]
                args.reverse()
                done_stack.append(self.reduce(top.x, tuple(args)))
                continue
            if isinstance(top, _UnbindOp):
                self.unbind(top.v)
                continue
            children = self.children(top)
            if isinstance(top, syntax.ELambda):
                self.bind(top.arg)
                work_stack.append(_UnbindOp(top.arg))
            work_stack.append(_ReduceOp(top, len(children)))
            work_stack.extend(reversed(children))
        assert len(done_stack) == 1
        return done_stack[0]

    def children(self, x):
        if isinstance(x, tuple) or isinstance(x, list):
            return x
        elif isinstance(x, dict):
            raise NotImplementedError()
        elif isinstance(x, common.ADT):
            return x.children()
        else:
            return ()

    def reduce(self, x, new_children):
        if isinstance(x, common.ADT):
            if all(a is b for (a, b) in zip(x.children(), new_children)):
                return x
            out = type(x)(*new_children)
            if isinstance(x, syntax.Exp) and hasattr(x, "type"):
                out = out.with_type(x.type)
            return out
        elif type(x) in [list, tuple, dict]:
            if type(x) in [list, tuple] and all(a is b for (a, b) in zip(x, new_children)):
                return x
            return type(x)(new_children)
        else:
            return x

def cse(e, verify=False):
    """
    Common subexpression elimination. Replaces re-used expressions with ELet,
    e.g. "(x+1) + (x+1)" ---> "let a = x+1 in a+a".
    """
    def finish(e, avail):
        ravail = collections.OrderedDict([(v, k) for (k, v) in avail.items() if v is not None])
        counts = free_vars(e, counts=True)
        for var, value in reversed(ravail.items()):
            for (vv, ct) in free_vars(value, counts=True).items():
                counts[vv] = counts.get(vv, 0) + ct
        to_inline = common.OrderedSet(v for v in ravail if counts.get(v, 0) < 2 or ravail[v].size() < 2)
        sub = { v : ravail[v] for v in to_inline }

        skip = collections.defaultdict(int)
        class V(IterativeReducer):
            def children(self, x):
                if isinstance(x, syntax.EVar) and x in sub and not skip[x]:
                    return (sub[x],)
                return super().children(x)
            def reduce(self, x, new_children):
                if isinstance(x, syntax.EVar) and x in sub and not skip[x]:
                    return new_children[0]
                return super().reduce(x, new_children)
            def bind(self, v):
                skip[v] += 1
            def unbind(self, v):
                skip[v] -= 1

        inliner = V()
        e = inliner.visit(e)

        for var, value in reversed(ravail.items()):
            if var in to_inline:
                continue
            value = inliner.visit(value)

            ee = syntax.ELet(value, target_syntax.ELambda(var, e))
            if hasattr(e, "type"):
                ee = ee.with_type(e.type)
            e = ee
        return e

    class V(BottomUpRewriter):
        def __init__(self):
            super().__init__()
            self.avail = ExpMap() # maps expressions --> variables
        def visit_EVar(self, e):
            return e
        def visit_ENum(self, e):
            return e
        def visit_EEnumEntry(self, e):
            return e
        def visit_EEmptyList(self, e):
            return e
        def visit_EStr(self, e):
            return e
        def visit_EBool(self, e):
            return e
        def visit_ENative(self, e):
            return e
        def visit_ENull(self, e):
            return e
        def visit_Exp(self, e):
            ee = type(e)(*[self.visit(c) for c in e.children()]).with_type(e.type)
            res = self.avail.get(ee)
            if res is not None:
                return res
            v = fresh_var(e.type, hint="tmp")
            self.avail[ee] = v
            return v
        def visit_EListComprehension(self, e):
            raise NotImplementedError()
        def _fvs(self, e):
            if not hasattr(e, "_fvs"):
                e._fvs = free_vars(e)
            return e._fvs
        def visit_ELambda(self, e):
            old_avail = self.avail
            self.avail = ExpMap([(k, v) for (k, v) in self.avail.items() if e.arg not in self._fvs(k)])
            body = self.visit(e.body)

            precious = set((e.arg,))
            # print("computing fvs x{}...".format(len(self.avail.items())))
            fvs = { v : self._fvs(k) for (k, v) in self.avail.items() }
            # print("done")
            dirty = True
            while dirty:
                dirty = False
                for v in self.avail.values():
                    if any(vv in precious for vv in fvs[v]):
                        if v not in precious:
                            precious.add(v)
                            dirty = True
            for (k, v) in list(self.avail.items()):
                if v not in precious:
                    old_avail[k] = v
                    del self.avail[k]

            body = finish(body, self.avail)
            self.avail = old_avail
            return target_syntax.ELambda(e.arg, body)

    v = V()
    res = v.visit(e)
    res = finish(res, v.avail)
    if verify:
        from cozy.solver import valid
        if not valid(syntax.EBinOp(e, "===", res).with_type(syntax.BOOL), model_callback=print):
            print(repr(e))
            assert False
    return res

def inline_calls(spec):
    extern_func_names = set(e.name for e in spec.extern_funcs)
    queries = {q.name : q for q in spec.methods if isinstance(q, syntax.Query)}

    class CallInliner(BottomUpRewriter):

        def visit_Spec(self, spec):
            spec = shallow_copy(spec)
            spec.methods = tuple(self.visit(m) for m in spec.methods if not (isinstance(m, syntax.Query) and m.visibility != syntax.Visibility.Public))
            return spec

        def visit_ECall(self, e):
            query = queries.get(e.func)

            if query is None:
                return e

            return self.visit(subst(query.ret,
                {arg: self.visit(expr) for ((arg, argtype), expr) in zip(query.args, e.args)}))

    rewriter = CallInliner()
    return rewriter.visit(spec)

def get_modified_var(stm):
    """
    Given a statement, returns a tuple:
    (
        the EVar modified by the statement (if any),
        the handle type modified by the statement (if any)
    )
    Returns (None, None) if there is no modification.
    """
    def find_lvalue_target(e):
        if isinstance(e, syntax.EVar):
            return e, None
        elif isinstance(e, target_syntax.EMapGet):
            return find_lvalue_target(e.map)[0], None
        elif isinstance(e, syntax.ETupleGet):
            return find_lvalue_target(e.e)[0], None
        elif isinstance(e, syntax.EGetField):
            if isinstance(e.e.type, syntax.THandle) and e.f == "val":
                handle_type = e.e.type
            else:
                handle_type = None
            return find_lvalue_target(e.e)[0], handle_type
        assert False, "unexpected modification target {}".format(e)

    if isinstance(stm, syntax.SAssign):
        return find_lvalue_target(stm.lhs)
    elif isinstance(stm, syntax.SCall):
        return find_lvalue_target(stm.target)
    elif isinstance(stm, (target_syntax.SMapPut, target_syntax.SMapDel,
                            target_syntax.SMapUpdate)):
        return find_lvalue_target(stm.map)
    else:
        return None, None

class ExpInfo(object):
    def __init__(self, tempvar, count, dependents, handle_types, paths):
        self.tempvar = tempvar
        self.count = count
        self.dependents = dependents
        self.handle_types = handle_types
        self.paths = paths

    def __repr__(self):
        return "<ExpInfo(tempvar={}, count={}, deps={}, handle_types={}, paths={})>".format(
            self.tempvar, self.count, self.dependents, self.handle_types, self.paths
        )

class ExpressionMap(ExpMap):
    """
    Maps expressions to (temp vars, other supporting info).
    """
    def set_or_increment(self, exp, dependents, handle_types, path):
        info = self.get(exp)

        if info is not None:
            # Expr has been seen before. (Dependents/types shouldn't change.)
            assert info.dependents == dependents
            assert info.handle_types == handle_types
            info.count += 1
            info.paths.append(path)
        else:
            # Never before seen expr.
            self[exp] = ExpInfo(fresh_var(exp.type, "tmp"), 1, set(dependents),
                set(handle_types), [path])

    def unbind_handle_type(self, handle_type):
        """
        Returns a new ExpressionMap without expressions related to the given
        handle type.
        """
        return ExpressionMap((exp, expinfo) for exp, expinfo in self.items()
            if handle_type.statevar not in expinfo.handle_types)

    def unbind(self, var):
        """
        Returns a new ExpressionMap without expressions related to the given var.
        """
        return ExpressionMap((exp, expinfo) for exp, expinfo in self.items()
            if var.id not in expinfo.dependents)

class SLinearSequence(syntax.Stm):
    """
    An intermediate form of SSeq that just holds a list of its ordered
    constituent statements.
    """
    def __init__(self, statements):
        self.statements = statements
    @classmethod
    def from_seq(cls, seq):
        return cls(list(break_seq(seq)))
    def children(self):
        return tuple(self.statements)
    def __repr__(self):
        return "SLinearSequence{}".format(repr(self.children()))

def cse_scan(e):
    SIMPLE_EXPS = (syntax.ENum, syntax.EVar, syntax.EBool, syntax.EStr,
        syntax.ENative, syntax.EEnumEntry, syntax.ENull, syntax.EEmptyList)

    class SeqTransformer(BottomUpRewriter):
        """Rewrites SSeq -> SLinearSequence for CSE process."""
        def visit_SSeq(self, s):
            return SLinearSequence.from_seq(s)

    class CSEScanner(PathAwareExplorer):
        def __init__(self):
            self.captures = collections.defaultdict(list)
            # And we want a map of expression path -> CSE temp var.
            self.rewrites = dict()

        def visit_object(self, o, path, *args, **kwargs):
            # Include empty dependents/handle types in result.
            return self.join(o, ()), set(), set()

        def visit_children(self, e, path, entries, capture_point):
            """
            Returns (expr, dependent_vars, handle types) for each child of e by
            visiting it.
            """
            assert isinstance(e, common.ADT)
            return [
                self.visit(c, path + (i,), entries, capture_point)
                for i, c in enumerate(e.children())
                if isinstance(c, syntax.ADT) # ignore non-ADT children, like strings.
                ]

        def filter_captured_vars(self, outer_entries, inner_entries,
                capture_path, bound_var, handle_capture=False):
            """
            Move things from inner_entries to capture/rewrite structures if
            they're related to the binding variable. Otherwise, bubble them up
            to the surrounding scope.
            """
            for expr, expinfo in inner_entries.items():
                if handle_capture:
                    # Capture based on handle type.
                    should_capture = bound_var.type.statevar in expinfo.handle_types
                else:
                    # Capture based on var name.
                    should_capture = bound_var.id in expinfo.dependents

                if should_capture:
                    if expinfo.count > 1 and type(expr) not in SIMPLE_EXPS:
                        self.captures[capture_path].append((expinfo.tempvar, expr))
                        self.rewrites.update({p: expinfo.tempvar for p in expinfo.paths})
                else:
                    # Bubble up to surrounding capture point.
                    outer_entries[expr] = expinfo

        def visit_ELambda(self, e, path, entries, capture_point):
            # Capture point changes with ELambda. (The body is the 1st child,
            # zero-indexed.)
            submap = entries.unbind(e.arg)
            _, deps, handle_types = self.visit(e.body, path + (1,), submap, e.body)
            e = e.with_type(e.body.type)
            entries.set_or_increment(e, deps, handle_types, path)
            self.filter_captured_vars(entries, submap, path + (1,), e.arg)
            return e, deps, handle_types

        def visit_SLinearSequence(self, s, path, entries, capture_point):
            def scan_statement_sequence(seq_pair, ordinal, inner_entries, inner_capture):
                if seq_pair is None:
                    # End of the fold.
                    return

                stm_path = path + (ordinal,)
                stm, rest = seq_pair if isinstance(seq_pair, tuple) else (seq_pair, None)

                killed_var, handle_type = get_modified_var(stm)
                is_handle_mod = handle_type is not None
                self.visit(stm, stm_path, inner_entries, inner_capture)

                if killed_var is not None:
                    # Unbind expressions related to killed_var
                    if is_handle_mod:
                        submap = inner_entries.unbind_handle_type(handle_type)
                    else:
                        submap = inner_entries.unbind(killed_var)

                    scan_statement_sequence(rest, ordinal + 1, submap, stm)
                    self.filter_captured_vars(inner_entries, submap, stm_path,
                        killed_var, is_handle_mod)
                else:
                    scan_statement_sequence(rest, ordinal + 1, inner_entries, inner_capture)

            # Do a right-fold over the sequence of statements.
            scan_statement_sequence(
                functools.reduce(lambda a, b: (b, a), reversed(s.statements)),
                0, entries, capture_point)

            return s, set(), set()

        def visit_SForEach(self, s, path, entries, capture_point):
            self.visit(s.iter, path + (1,), entries, capture_point)
            # Capture point changes with SForEach. (The body is the child 2,
            # zero-indexed.)
            submap = entries.unbind(s.id)
            self.visit(s.body, path + (2,), submap, s.body)
            self.filter_captured_vars(entries, submap, path + (2,), s.id)
            return s, set(), set()

        def visit_Exp(self, e, path, entries, capture_point):
            deps = set()
            handle_types = set()

            for _, subdeps, subhandles in self.visit_children(e, path, entries, capture_point):
                deps |= subdeps
                handle_types |= subhandles

            entries.set_or_increment(e, deps, handle_types, path)
            return e, deps, handle_types

        def visit_EVar(self, e, path, entries, capture_point):
            # The genesis of variable dependence & type tracking.
            deps = {e.id}

            if isinstance(e.type, syntax.THandle):
                handle_types = {e.type.statevar}
            else:
                handle_types = set()

            entries.set_or_increment(e, deps, handle_types, path)
            return e, deps, handle_types

    seq_rewriter = SeqTransformer()
    e = seq_rewriter.visit(e)

    entries = ExpressionMap()
    scanner = CSEScanner()
    result = scanner.visit(e, (), entries, e)

    # Anything remaining here gets assigned to the top-level capture point.
    for expr, expr_info in entries.items():
        if expr_info.count > 1 and not isinstance(expr, SIMPLE_EXPS):
            scanner.captures[()].append((expr_info.tempvar, expr))
            scanner.rewrites.update({p: expr_info.tempvar for p in expr_info.paths})

    # Remove captures that aren't actually present in the rewrites.

    def tuple_prefixes(t):
        """
        Generates all prefixes of the given tuple in ascending order of length,
        not including t itself.
        """
        return (t[:i] for i in range(len(t)))

    final_rewrites = dict()
    used_temp_names = set()

    # rewrites contains paths that WILL get rewritten. Some are wholly contained
    # within others, so we only need to worry about the outer paths. Sort by
    # length of path so that outer paths are considered before the inner ones.
    for path, tempvar in sorted(scanner.rewrites.items(), key=lambda x: len(x[0])):
        if all(prefix not in final_rewrites for prefix in tuple_prefixes(path)):
            final_rewrites[path] = tempvar
            used_temp_names.add(tempvar.id)

    final_captures = {
        path: list(filter(lambda d: (d[0].id in used_temp_names), captures))
        for path, captures in scanner.captures.items()
    }

    return e, final_captures, final_rewrites

class CSERewriter(PathAwareRewriter):
    def __init__(self, capture_map, rewrite_map):
        self.capture_map = capture_map
        self.rewrite_map = rewrite_map
        self.did_alter_tree = False

    def _visit_atom(self, e, path):
        return e

    # atoms -- no subexpressions.
    visit_EVar = visit_ENum = visit_EEnumEntry = visit_EEmptyList = \
        visit_EStr = visit_EBool = visit_ENative = visit_ENull = \
        _visit_atom

    def visit_Exp(self, e, path):
        def visit_default(exp):
            return type(exp)(
                *[self.visit(c, path + (i,)) for i, c in enumerate(exp.children())]
            ).with_type(exp.type)

        rewrites = self.capture_map.get(path)

        if rewrites is not None:
            e = visit_default(e)

            for temp, expr in reversed(rewrites):
                e = syntax.ELet(expr, target_syntax.ELambda(temp, e)).with_type(e.type)
                self.did_alter_tree = True
            return e
        else:
            rewrite = self.rewrite_map.get(path)
            if rewrite is not None:
                self.did_alter_tree = True
                return rewrite
            else:
                return visit_default(e)

    def visit_Stm(self, s, path):
        def visit_default(exp):
            return type(exp)(
                *[self.visit(c, path + (i,)) for i, c in enumerate(exp.children())]
            )

        s = visit_default(s)

        for temp, expr in reversed(self.capture_map.get(path, ())):
            s = syntax.SSeq(syntax.SDecl(temp.id, expr), s)
            self.did_alter_tree = True

        return s

    def visit_SLinearSequence(self, s, path):
        """
        Each of s.statements are Stm instances. Some of them have
        capture_map entries. We may expand this list into a longer one
        depending on capture_map.
        e.g.,
        [s1, s2, s3] -> [tmp1 = x+1, s1, tmp2=y+1, s2, s3]
        """

        output = [syntax.SDecl(temp.id, expr)
            for temp, expr in reversed(self.capture_map.get(path, ()))]

        # i is the original index of the child at scan time.

        for i, stm in enumerate(s.statements):
            child_path = path + (i,)

            stm = type(stm)(*[self.visit(c, child_path + (j,))
                for j, c in enumerate(stm.children())])

            # Emit the original expression *before* any capture rewrites.
            output.append(stm)

            output.extend(syntax.SDecl(temp.id, expr)
                for temp, expr in reversed(self.capture_map.get(child_path, ())))

        if len(s.statements) < len(output):
            self.did_alter_tree = True

        return syntax.seq(output)

def cse_replace(elem):
    """
    Eliminate common subexpressions on an AST element (an expression or a
    statement -- not a full spec).
    """
    # Fixed point routine that stops when eliminations stop occurring.
    while True:
        e_scan, capture_map, rewrite_map = cse_scan(elem)

        if not capture_map:
            # Nothing to replace.
            break

        rewriter = CSERewriter(capture_map, rewrite_map)
        elem = rewriter.visit(e_scan, ())

        if not rewriter.did_alter_tree:
            break

    return fix_conditionals(elem)

def cse_replace_spec(spec):
    """
    Eliminate common subexprs on a spec. Internally, this applies to Ops.
    """
    class OpVisitor(BottomUpRewriter):
        def visit_Op(self, s):
            s.body = cse_replace(s.body)
            return s

    op_visitor = OpVisitor()
    return op_visitor.visit(spec)

class UseType(Enum):
    USED_NEVER = 0
    USED_SOMETIMES = 1
    USED_ALWAYS = 2

USED_NEVER = UseType.USED_NEVER
USED_SOMETIMES = UseType.USED_SOMETIMES
USED_ALWAYS = UseType.USED_ALWAYS

class ConditionalUseFinder(BottomUpExplorer):
    """
    Computes whether the given var is always, sometimes, or never used in a tree.
    """
    def __init__(self, var):
        self.var = var

    def visit_Exp(self, e):
        child_uses = set(self.visit(child) for child in e.children())

        if USED_ALWAYS in child_uses:
            return USED_ALWAYS
        elif USED_SOMETIMES in child_uses:
            return USED_SOMETIMES
        else:
            return USED_NEVER

    def visit_ECond(self, e):
        cond_use_type = self.visit(e.cond)

        if cond_use_type == USED_ALWAYS:
            return USED_ALWAYS

        e1_use_type = self.visit(e.then_branch)
        e2_use_type = self.visit(e.else_branch)

        if e1_use_type == USED_ALWAYS and e2_use_type == USED_ALWAYS:
            return USED_ALWAYS
        elif cond_use_type == USED_SOMETIMES:
            return USED_SOMETIMES
        elif e1_use_type == USED_ALWAYS or e2_use_type == USED_ALWAYS:
            return USED_SOMETIMES
        elif e1_use_type == USED_SOMETIMES or e2_use_type == USED_SOMETIMES:
            return USED_SOMETIMES
        else:
            return USED_NEVER

    visit_Stm = visit_Exp
    visit_SIf = visit_ECond

    def visit_EVar(self, v):
        return USED_ALWAYS if v == self.var else USED_NEVER

    def visit_object(self, o):
        return USED_NEVER

def introduce_decl(var : syntax.EVar, value : syntax.Exp, thing):
    if isinstance(thing, syntax.Stm):
        return syntax.SSeq(syntax.SDecl(var.id, value), thing)
    if isinstance(thing, syntax.Exp):
        return syntax.ELet(value, syntax.ELambda(var, thing)).with_type(thing.type)
    raise ValueError(thing)

def push_decl(var : syntax.EVar, value : syntax.Exp, thing):
    if isinstance(thing, tuple) or isinstance(thing, list):
        return tuple(push_decl(var, value, x) for x in thing)
    if isinstance(value, syntax.EVar):
        return subst(thing, {var.id:value})
    if isinstance(thing, syntax.ELambda):
        assert var != thing.arg
        return syntax.ELambda(thing.arg, push_decl(var, value, thing.body))
    if not isinstance(thing, common.ADT):
        return thing
    use_type = ConditionalUseFinder(var).visit(thing)
    if use_type == USED_NEVER:
        return thing
    if use_type == USED_ALWAYS:
        return introduce_decl(var, value, thing)
    if use_type == USED_SOMETIMES:
        new_children = tuple(push_decl(var, value, child) for child in thing.children())
        res = type(thing)(*new_children)
        if isinstance(thing, syntax.Exp):
            res = res.with_type(thing.type)
        return res

class BindingRewriter(BottomUpRewriter):
    """
    Considers variable bindings and moves them into conditional structures in
    the tree based on whether they're always, sometimes, or never used in those
    structures.
    """

    def visit_ELet(self, e):
        return push_decl(e.f.arg, e.e, self.visit(e.f.body))

    def visit_SSeq(self, seq):
        parts = [self.visit(part) for part in break_seq(seq)]
        res = parts[-1]
        for i in reversed(range(len(parts) - 1)):
            p = parts[i]
            if isinstance(p, syntax.SDecl):
                decl_var = syntax.EVar(p.id).with_type(p.val.type)
                res = push_decl(decl_var, p.val, res)
            else:
                res = syntax.SSeq(p, res)
        return syntax.seq(break_seq(res))

def fix_conditionals(e):
    rewriter = BindingRewriter()
    return rewriter.visit(e)

def is_lvalue(e : syntax.Exp) -> bool:
    if isinstance(e, syntax.EVar):
        return True
    if isinstance(e, syntax.EGetField):
        return True
    if isinstance(e, syntax.EListGet):
        return True
    if isinstance(e, target_syntax.EMapGet):
        return True
    return False
