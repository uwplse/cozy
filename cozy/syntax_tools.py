"""
Various utilities for working with syntax trees.

    pprint(ast) -> str            prettyprint a syntax tree

"""

import sys
import itertools

from cozy import common
from cozy import syntax
from cozy import target_syntax

def fresh_var(type, hint="var"):
    return syntax.EVar(common.fresh_name(hint)).with_type(type)

def mk_lambda(t, l):
    v = fresh_var(t)
    return target_syntax.ELambda(v, l(v))

def compose(f1 : target_syntax.ELambda, f2 : target_syntax.ELambda) -> target_syntax.ELambda:
    return mk_lambda(f2.arg.type, lambda v: f1.apply_to(f2.apply_to(v)))

_SCALAR_TYPES = set((
    syntax.TInt,
    syntax.TLong,
    syntax.TBool,
    syntax.TString,
    syntax.TNative,
    syntax.THandle,
    syntax.TEnum))
def is_scalar(t : syntax.Type):
    if type(t) in _SCALAR_TYPES:
        return True
    if isinstance(t, syntax.TTuple):
        return all(is_scalar(tt) for tt in t.ts)
    if isinstance(t, syntax.TRecord):
        return all(is_scalar(tt) for (f, tt) in t.fields)
    if isinstance(t, syntax.TMaybe):
        return is_scalar(t.t)
    return False

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
            out = type(x)(*new_children)
        elif type(x) in [list, tuple, dict]:
            out = type(x)(new_children)
        else:
            out = x
        if isinstance(x, syntax.Exp) and hasattr(x, "type"):
            out.type = x.type
        if isinstance(x, syntax.THandle) and hasattr(x, "value_type"):
            out.value_type = x.value_type
        return out

def deep_copy(ast):
    return BottomUpRewriter().visit(ast)

def shallow_copy(ast):
    return BottomUpRewriter().join(ast, ast.children())

def all_types(ast):
    class TypeCollector(BottomUpExplorer):
        def visit_Type(self, t):
            yield from super().visit_ADT(t)
            yield t
        def visit_object(self, o):
            return ()
        def join(self, t, children):
            return itertools.chain(*children)
    return common.unique(TypeCollector().visit(ast))

class PrettyPrinter(common.Visitor):
    def visit_Spec(self, spec):
        s = spec.name + ":\n"
        for name, t in spec.types:
            s += "  type {} = {}\n".format(name, self.visit(t))
        for name, t in spec.statevars:
            s += "  state {} : {}\n".format(name, self.visit(t))
        for e in spec.assumptions:
            s += "  assume {};\n".format(self.visit(e))
        for op in spec.methods:
            s += str(self.visit(op))
        return s

    def visit_TEnum(self, enum):
        return "enum {{ {} }}".format(", ".join(enum.cases))

    def visit_TNamed(self, named):
        return named.id

    def visit_TNative(self, t):
        return t.name

    def visit_TApp(self, app):
        return "{}<{}>".format(app.t, self.visit(app.args))

    def visit_TBag(self, s):
        return "Bag<{}>".format(self.visit(s.t))

    def visit_TSet(self, s):
        return "Set<{}>".format(self.visit(s.t))

    def visit_TMap(self, m):
        return "Map<{}, {}>".format(self.visit(m.k), self.visit(m.v))

    def visit_THeap(self, h):
        return "Heap<{}>".format(self.visit(h.t))

    def visit_TLinkedList(self, h):
        return "LinkedList<{}>".format(self.visit(h.t))

    def visit_THashMap(self, h):
        return "HashMap<{}, {}>".format(self.visit(h.k), self.visit(h.v))

    def visit_TInt(self, t):
        return "Int"

    def visit_TLong(self, t):
        return "Long"

    def visit_TBool(self, t):
        return "Bool"

    def visit_TString(self, t):
        return "String"

    def visit_TMaybe(self, t):
        return "Maybe<{}>".format(self.visit(t.t))

    def visit_TTuple(self, t):
        return "({})".format(", ".join(self.visit(tt) for tt in t.ts))

    def visit_TRecord(self, r):
        return "{{ {} }}".format(", ".join("{} : {}".format(f, self.visit(t)) for f, t in r.fields))

    def visit_THandle(self, t):
        return t.statevar

    def visit_ConcreteType(self, t):
        return t.prettyprint()

    def visit_Query(self, q):
        s = "  query {}({}):\n".format(q.name, ", ".join("{} : {}".format(name, self.visit(t)) for name, t in q.args))
        for e in q.assumptions:
            s += "    assume {};\n".format(self.visit(e))
        s += "    {}\n".format(self.visit(q.ret))
        return s

    def visit_Op(self, q):
        s = "  op {}({}):\n".format(q.name, ", ".join("{} : {}".format(name, self.visit(t)) for name, t in q.args))
        for e in q.assumptions:
            s += "    assume {};\n".format(self.visit(e))
        s += "{}\n".format(self.visit(q.body, "    "))
        return s

    def visit_EVar(self, e):
        return e.id

    def visit_EBool(self, e):
        return "true" if e.val else "false"

    def visit_ENum(self, e):
        return str(e.val)

    def visit_EEnumEntry(self, e):
        return e.name

    def visit_EJust(self, e):
        return "Just({})".format(self.visit(e.e))

    def visit_ENull(self, e):
        return "NULL"

    def visit_ELambda(self, e):
        if hasattr(e.arg, "type"):
            return "(\\{} : {} -> {})".format(e.arg.id, self.visit(e.arg.type), self.visit(e.body))
        return "(\\{} -> {})".format(e.arg.id, self.visit(e.body))

    def visit_EApp(self, e):
        return "{}({})".format(self.visit(e.f), self.visit(e.arg))

    def visit_EAlterMaybe(self, e):
        return "AlterMaybe({}, {})".format(self.visit(e.e), self.visit(e.f))

    def visit_EMapGet(self, e):
        return "{}[{}]".format(self.visit(e.map), self.visit(e.key))

    def visit_EMakeMap(self, e):
        return "MkMap({}, {}, {})".format(self.visit(e.e), self.visit(e.key), self.visit(e.value))

    def visit_EMap(self, e):
        return "Map {{{}}} ({})".format(self.visit(e.f), self.visit(e.e))

    def visit_EFilter(self, e):
        return "Filter {{{}}} ({})".format(self.visit(e.p), self.visit(e.e))

    def visit_EFlatten(self, e):
        return "Flatten({})".format(self.visit(e.e))

    def visit_EFlatMap(self, e):
        return "FlatMap({}, {})".format(self.visit(e.e), self.visit(e.f))

    def visit_EBinOp(self, e):
        return "({} {} {})".format(self.visit(e.e1), e.op, self.visit(e.e2))

    def visit_ECond(self, e):
        return "({} ? {} : {})".format(self.visit(e.cond), self.visit(e.then_branch), self.visit(e.else_branch))

    def visit_EUnaryOp(self, e):
        return "({} {})".format(e.op, self.visit(e.e))

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
        return "new {}({})".format(self.visit(e.t), ", ".join(self.visit(arg) for arg in e.args))

    def visit_ECall(self, e):
        return "{}({})".format(e.func, ", ".join(self.visit(arg) for arg in e.args))

    def visit_ETuple(self, e):
        return "({})".format(", ".join(self.visit(e) for e in e.es))

    def visit_ETupleGet(self, e):
        return "({}).{}".format(self.visit(e.e), e.n)

    def visit_ELet(self, e):
        return "let {} = {} in {}".format(e.f.arg.id, self.visit(e.e), self.visit(e.f.body))

    def visit_CPull(self, c):
        return "{} <- {}".format(c.id, self.visit(c.e))

    def visit_CCond(self, c):
        return self.visit(c.e)

    def visit_ADT(self, e, *args, **kwargs):
        return "{}({})".format(type(e).__name__, ", ".join(self.visit(x) for x in e.children()))

    def visit_object(self, e, *args, **kwargs):
        print("Warning: implement prettyprinting for {}".format(type(e).__name__), file=sys.stderr)
        return repr(e)

    def visit_SNoOp(self, s, indent=""):
        return "{}pass".format(indent)

    def visit_SCall(self, s, indent=""):
        return "{}{}.{}({})".format(indent, self.visit(s.target), s.func, ", ".join(self.visit(arg) for arg in s.args))

    def visit_SAssign(self, s, indent=""):
        return "{}{} = {}".format(indent, self.visit(s.lhs), self.visit(s.rhs))

    def visit_SDecl(self, s, indent=""):
        return "{}var {} : {} = {}".format(indent, s.id, self.visit(s.val.type), self.visit(s.val))

    def visit_SDel(self, s, indent=""):
        return "{}del {}".format(indent, self.visit(s.e))

    def visit_SSeq(self, s, indent=""):
        return "{}\n{}".format(self.visit(s.s1, indent), self.visit(s.s2, indent))

    def visit_SMapUpdate(self, s, indent=""):
        return "{indent}with {} as {}:\n{}".format(
            self.visit(target_syntax.EMapGet(s.map, s.key)),
            s.val_var.id,
            self.visit(s.change, indent + "  "),
            indent=indent)

    def visit_SMapPut(self, s, indent=""):
        return "{indent}{} = {}".format(
            self.visit(target_syntax.EMapGet(s.map, s.key)),
            self.visit(s.value),
            indent=indent)

    def visit_SMapDel(self, s, indent=""):
        return "{indent}del {}".format(
            self.visit(target_syntax.EMapGet(s.map, s.key)),
            indent=indent)

    def visit_SForEach(self, s, indent=""):
        return "{}for {} in {}:\n{}".format(indent, s.id.id, self.visit(s.iter), self.visit(s.body, indent + "  "))

    def visit_SIf(self, s, indent=""):
        if isinstance(s.else_branch, syntax.SNoOp):
            return "{indent}if {}:\n{}".format(self.visit(s.cond), self.visit(s.then_branch, indent + "  "), indent=indent)
        return "{indent}if {}:\n{}\n{indent}else:\n{}".format(self.visit(s.cond), self.visit(s.then_branch, indent + "  "), self.visit(s.else_branch, indent + "  "), indent=indent)

_PRETTYPRINTER = PrettyPrinter()
def pprint(ast):
    return _PRETTYPRINTER.visit(ast)

def free_vars(exp):

    class VarCollector(common.Visitor):
        def __init__(self):
            self.bound = []

        def visit_EVar(self, e):
            if e.id not in self.bound:
                yield e

        def visit_EMakeRecord(self, e):
            for f, ee in e.fields:
                yield from self.visit(ee)

        def visit_EListComprehension(self, e):
            return self.visit_clauses(e.clauses, 0, e.e)

        def visit_clauses(self, clauses, i, e):
            if i >= len(clauses):
                yield from self.visit(e)
                return
            c = clauses[i]
            if isinstance(c, syntax.CPull):
                yield from self.visit(c.e)
                self.bound.append(c.id)
                yield from self.visit_clauses(clauses, i + 1, e)
                del self.bound[-1]
            elif isinstance(c, syntax.CCond):
                yield from self.visit(c.e)
                yield from self.visit_clauses(clauses, i + 1, e)
            else:
                raise Exception("unknown case: {}".format(c))

        def visit_EAlloc(self, e):
            for ee in e.args:
                yield from self.visit(ee)

        def visit_ECall(self, e):
            for ee in e.args:
                yield from self.visit(ee)

        def visit_ETuple(self, e):
            for ee in e.es:
                yield from self.visit(ee)

        def visit_ELambda(self, e):
            for v in self.visit(e.body):
                if v.id != e.arg.id:
                    yield v

        def visit_Query(self, q):
            args = set(arg_name for (arg_name, arg_type) in q.args)
            for v in itertools.chain(self.visit(q.ret), *[self.visit(a) for a in q.assumptions]):
                if v.id not in args:
                    yield v

        def visit_Exp(self, e):
            for child in e.children():
                if isinstance(child, syntax.Exp):
                    yield from self.visit(child)

        def visit_object(self, o):
            raise NotImplementedError(type(o))

    return common.OrderedSet(VarCollector().visit(exp))

def all_exps(e):
    class V(BottomUpExplorer):
        def join(self, x, children):
            for child in children:
                yield from child
            if isinstance(x, syntax.Exp):
                yield x
    return V().visit(e)

class FragmentEnumerator(common.Visitor):
    # This visitor's methods use a weird pattern:
    #     yield (lambda r: ...)(r)
    # This is because lambdas are capture-by-reference in Python! Since r is
    # overwritten at each loop iteration, that's a problem. Defining a fresh
    # function and immediately calling it is a simple way to force
    # capture-by-value for r instead.

    def visit_ELambda(self, obj):
        yield ([], obj, lambda x: x)

    def visit_EFilter(self, e):
        yield ([], e, lambda x: x)
        t = e.type
        for (a, x, r) in self.visit(e.e):
            yield (lambda r: (a, x, lambda x: target_syntax.EFilter(r(x), e.p).with_type(t)))(r)
        for (a, x, r) in self.visit(e.p.body):
            yield (lambda r: (a + [syntax.EBinOp(e.p.arg, syntax.BOp.In, e.e).with_type(syntax.BOOL)], x, lambda x: target_syntax.EFilter(e.e, target_syntax.ELambda(e.p.arg, r(x))).with_type(t)))(r)

    def visit_EMap(self, e):
        yield ([], e, lambda x: x)
        t = e.type
        for (a, x, r) in self.visit(e.e):
            yield (lambda r: (a, x, lambda x: target_syntax.EMap(r(x), e.f).with_type(t)))(r)
        for (a, x, r) in self.visit(e.f.body):
            yield (lambda r: (a + [syntax.EBinOp(e.f.arg, syntax.BOp.In, e.e).with_type(syntax.BOOL)], x, lambda x: target_syntax.EMap(e.e, target_syntax.ELambda(e.f.arg, r(x))).with_type(t)))(r)

    def visit_EFlatMap(self, e):
        yield ([], e, lambda x: x)
        t = e.type
        for (a, x, r) in self.visit(e.e):
            yield (lambda r: (a, x, lambda x: target_syntax.EFlatMap(r(x), e.f).with_type(t)))(r)
        for (a, x, r) in self.visit(e.f.body):
            yield (lambda r: (a + [syntax.EBinOp(e.f.arg, syntax.BOp.In, e.e).with_type(syntax.BOOL)], x, lambda x: target_syntax.EFlatMap(e.e, target_syntax.ELambda(e.f.arg, r(x))).with_type(t)))(r)

    def visit_Exp(self, obj):
        yield ([], obj, lambda x: x)
        t = obj.type
        children = obj.children()
        for i in range(len(children)):
            for (a, x, r) in self.visit(children[i]):
                yield (a, x, (lambda r, i: lambda x: type(obj)(*(children[:i] + (r(x),) + children[i+1:])).with_type(t))(r, i))

    def visit_list(self, l):
        return self.visit_tuple(l)

    def visit_tuple(self, t):
        yield ([], t, lambda x: x)
        for i in range(len(t)):
            for (a, x, r) in self.visit(t[i]):
                yield (a, x, (lambda r, i: lambda x: t[:i] + (r(x),) + t[i+1:])(r, i))

    def visit_object(self, obj):
        yield ([], obj, lambda x: x)

_ENUMERATOR = FragmentEnumerator()
def enumerate_fragments(e : syntax.Exp):
    """
    Yields tuples (a : [Exp], x : Exp, r : Exp->Exp) such that:
        x is a non-lambda subexpression of e
        a are true assumptions whenever x is evaluated on any input to e
        r(x) == e (in general, r can be used to replace x with a new subexpr)
    """
    for tup in _ENUMERATOR.visit(e):
        (a, x, r) = tup
        if isinstance(x, syntax.Exp) and not isinstance(x, target_syntax.ELambda):
            yield tup

def replace(exp, old_exp, new_exp):
    class Replacer(BottomUpRewriter):
        def visit_ELambda(self, e):
            return target_syntax.ELambda(e.arg, self.visit(e.body))
        def visit(self, e):
            if e == old_exp:
                return new_exp
            return super().visit(e)
    return Replacer().visit(exp)

@common.typechecked
def re_use(e : syntax.Exp, target):
    return mk_lambda(e.type, target).apply_to(e)

def subst(exp, replacements):
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
                if any(v.id == d.id for r in replacements.values() for v in free_vars(r)):
                    raise NotImplementedError()
                if c.id in allfvs:
                    name = common.fresh_name()
                    r = { c.id : syntax.EVar(name) }
                    e = subst(e, r)
                    for j in range(i + 1, len(clauses)):
                        d = clauses[j]
                        if isinstance(d, syntax.CPull):
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
        def visit_ELambda(self, e):
            m = replacements
            if e.arg.id in replacements:
                m = dict(m)
                del m[e.arg.id]
            arg = e.arg
            body = e.body
            while any(arg in free_vars(r) for r in replacements.values()):
                new_arg = fresh_var(arg.type)
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
                q.args,
                [subst(a, m) for a in q.assumptions],
                subst(q.ret, m))
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
                subst(o.body, m))
        def visit(self, x, *args, **kwargs):
            res = super().visit(x, *args, **kwargs)
            if isinstance(res, syntax.Exp) and hasattr(x, "type") and not hasattr(res, "type"):
                res.type = x.type
            return res

    return Subst().visit(exp)

def alpha_equivalent(e1, e2, allow_rename=lambda v1, v2: False):
    """
    Equality on expression ASTs is syntactic equality; even variable names are
    compared. So,
        [x | x <- L] != [y | y <- L].
    However, alpha equivalence allows renaming of variables, so
        alpha_equivalent([x | x <- L], [y | y <- L]) == True.

    The allow_rename parameter lets the programmer specify that some variables
    may be renamed into others. For instance, if allow_rename(y, z) == True,
    then the expressions "x+y" and "x+z" will be treated as alpha equivalent.
    """
    class V(common.Visitor):
        def __init__(self):
            self.remap = { } # maps e1 varnames ---> e2 varnames
        def visit_EVar(self, e1, e2):
            if not isinstance(e2, syntax.EVar):
                return False
            e1id = e1.id
            if allow_rename(e1, e2):
                if e1.id not in self.remap:
                    e1id = e2.id
                    self.remap[e1.id] = e1id
                else:
                    e1id = self.remap[e1.id]
            elif e1.id in self.remap:
                e1id = self.remap[e1.id]
            return e1id == e2.id
        def visit_ETuple(self, e1, e2):
            if not isinstance(e2, syntax.ETuple):
                return False
            return all(self.visit(ee1, ee2) for (ee1, ee2) in zip(e1.es, e2.es))
        def visit_ELambda(self, e1, e2):
            if not isinstance(e2, target_syntax.ELambda):
                return False
            with common.extend(self.remap, e1.arg.id, e2.arg.id):
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
                with common.extend(self.remap, c1.id, c2.id):
                    return self.visit_clauses(i + 1, clauses1, clauses2, e1, e2)
            elif isinstance(c1, syntax.CCond):
                return self.visit(c1.e, c2.e) and self.visit_clauses(i + 1, clauses1, clauses2, e1, e2)
            else:
                raise NotImplementedError(pprint(c1))
        def visit_str(self, s1, s2):
            return s1 == s2
        def visit_int(self, i1, i2):
            return i1 == i2
        def visit_ECall(self, e1, e2):
            if not isinstance(e2, syntax.ECall):
                return False
            return e1.func == e2.func and len(e1.args) == len(e2.args) and all(self.visit(a1, a2) for (a1, a2) in zip(e1.args, e2.args))
        def visit_Exp(self, e1, e2):
            if type(e1) is not type(e2):
                return False
            return all(self.visit(x, y) for (x, y) in zip(e1.children(), e2.children()))
        def visit_Query(self, q1, q2):
            if type(q2) is not syntax.Query:
                return False
            if len(q1.args) != len(q2.args):
                return False
            with common.extend_multi(self.remap, [(arg1, arg2) for ((arg1, type1), (arg2, type2)) in zip(q1.args, q2.args)]):
                # TODO: assumptions
                return self.visit(q1.ret, q2.ret)
        def visit_object(self, o, *args):
            raise NotImplementedError("{} ({})".format(type(o), repr(o)))

    return V().visit(e1, e2)

BOOL = syntax.TBool()

def implies(e1, e2):
    return syntax.EBinOp(
        syntax.EUnaryOp("not", e1).with_type(BOOL),
        "or",
        e2).with_type(BOOL)

def equal(e1, e2):
    return syntax.EBinOp(e1, "==", e2).with_type(BOOL)

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
    return [[e]]

def break_conj(e):
    if isinstance(e, syntax.EBinOp) and e.op == "and":
        yield from break_conj(e.e1)
        yield from break_conj(e.e2)
    else:
        yield e
