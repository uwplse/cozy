"""
Various utilities for working with syntax trees.

    pprint(ast) -> str            prettyprint a syntax tree

"""

import sys

import common
import syntax
import library

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

    def visit_TApp(self, app):
        return "{}<{}>".format(app.t, self.visit(app.args))

    def visit_TSet(self, s):
        return "Set<{}>".format(self.visit(s.t))

    def visit_TList(self, l):
        return "List<{}>".format(self.visit(l.t))

    def visit_TMap(self, m):
        return "Map<{}, {}>".format(self.visit(m.k), self.visit(m.v))

    def visit_THeap(self, h):
        return "Heap<{}>".format(self.visit(h.t))

    def visit_TInt(self, t):
        return "Int"

    def visit_TLong(self, t):
        return "Long"

    def visit_TBool(self, t):
        return "Bool"

    def visit_TRecord(self, r):
        return "{{ {} }}".format(", ".join("{} : {}".format(f, self.visit(t)) for f, t in r.fields))

    def visit_Type(self, t):
        if isinstance(t, library.ConcreteType):
            return type(t).__name__
        else:
            print("Warning: implement visit_{} in pprint".format(type(t).__name__), file=sys.stderr)
            return "??"

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

    def visit_EBinOp(self, e):
        return "({} {} {})".format(self.visit(e.e1), e.op, self.visit(e.e2))

    def visit_EUnaryOp(self, e):
        return "({} {})".format(e.op, self.visit(e.e))

    def visit_EGetField(self, e):
        return "({}).{}".format(self.visit(e.e), e.f)

    def visit_EMakeRecord(self, e):
        return "{{ {} }}".format(", ".join("{} : {}".format(name, val) for name, val in e.fields))

    def visit_EEmptyList(self, e):
        return "[]"

    def visit_EListComprehension(self, e):
        return "[{} | {}]".format(self.visit(e.e), ", ".join(self.visit(clause) for clause in e.clauses))

    def visit_EAlloc(self, e):
        return "new {}({})".format(self.visit(e.t), ", ".join(self.visit(arg) for arg in e.args))

    def visit_ECall(self, e):
        return "{}({})".format(e.func, ", ".join(self.visit(arg) for arg in e.args))

    def visit_ETuple(self, e):
        return "({})".format(", ".join(self.visit(e) for e in e.es))

    def visit_ELet(self, e):
        return "let {} = {} in {}".format(e.id, self.visit(e.e1), self.visit(e.e2))

    def visit_CPull(self, c):
        return "{} <- {}".format(c.id, self.visit(c.e))

    def visit_CCond(self, c):
        return self.visit(c.e)

    def visit_SNoOp(self, s, indent=""):
        return "{}pass".format(indent)

    def visit_SCall(self, s, indent=""):
        return "{}{}.{}({})".format(indent, s.target, s.func, ", ".join(self.visit(arg) for arg in s.args))

    def visit_SAssign(self, s, indent=""):
        return "{}{} = {}".format(indent, self.visit(s.lhs), self.visit(s.rhs))

    def visit_SDel(self, s, indent=""):
        return "{}del {}".format(indent, self.visit(s.e))

    def visit_SSeq(self, s, indent=""):
        return "{}\n{}".format(self.visit(s.s1, indent), self.visit(s.s2, indent))

    def visit_SForEach(self, s, indent=""):
        return "{}for {} in {}:\n{}".format(indent, s.id, self.visit(s.iter), self.visit(s.body, indent + "  "))

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

        def visit_EBool(self, e):
            return ()

        def visit_ENum(self, e):
            return ()

        def visit_EBinOp(self, e):
            yield from self.visit(e.e1)
            yield from self.visit(e.e2)

        def visit_EUnaryOp(self, e):
            return self.visit(e.e)

        def visit_EGetField(self, e):
            return self.visit(e.e)

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

    return set(VarCollector().visit(exp))

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
    for fvs in (free_vars(val) for val in replacements.values()):
        allfvs |= {fv.id for fv in fvs}

    class Subst(common.Visitor):
        def visit_EBool(self, b):
            return b
        def visit_ENum(self, n):
            return n
        def visit_EVar(self, var):
            return replacements.get(var.id, var)
        def visit_EBinOp(self, op):
            return syntax.EBinOp(self.visit(op.e1), op.op, self.visit(op.e2))
        def visit_EUnaryOp(self, op):
            return syntax.EUnaryOp(op.op, self.visit(op.e))
        def visit_EListComprehension(self, lcmp):
            return self.visit_lcmp(list(lcmp.clauses), 0, lcmp.e)
        def visit_lcmp(self, clauses, i, e):
            if i >= len(clauses):
                return syntax.EListComprehension(self.visit(e), clauses)
            c = clauses[i]
            if isinstance(c, syntax.CPull):
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
                    clauses[i] = syntax.CPull(name, self.visit(c.e))
                return self.visit_lcmp(clauses, i + 1, e)
            elif isinstance(c, syntax.CCond):
                clauses[i] = syntax.CCond(self.visit(c.e))
                return self.visit_lcmp(clauses, i + 1, e)
        def visit_ECall(self, e):
            return syntax.ECall(e.func, [self.visit(arg) for arg in e.args])

    return Subst().visit(exp)

def alpha_equivalent(e1, e2):
    """
    Equality on expression ASTs is syntactic equality; even variable names are
    compared. So,
        [x | x <- L] != [y | y <- L].
    However, alpha equivalence allows renaming of non-free variables, so
        alpha_equivalent([x | x <- L], [y | y <- L]) == True.
    """
    class V(common.Visitor):
        def __init__(self):
            self.remap = { } # maps e1 varnames ---> e2 varnames
        def visit_EVar(self, e1, e2):
            if not isinstance(e2, syntax.EVar):
                return False
            e1id = self.remap.get(e1.id, e1.id)
            return e1id == e2.id
        def visit_ENum(self, e1, e2):
            return isinstance(e2, syntax.ENum) and e1.val == e2.val
        def visit_EBool(self, e1, e2):
            return isinstance(e2, syntax.EBool) and e1.val == e2.val
        def visit_EEmptyList(self, e1, e2):
            if isinstance(e2, syntax.EEmptyList):
                return True
            return False
        def visit_EListComprehension(self, lcmp, other):
            if not isinstance(other, syntax.EListComprehension):
                return False
            if len(lcmp.clauses) != len(other.clauses):
                return False
            return self.visit_clauses(0, lcmp.clauses, other.clauses, lcmp.e, other.e)
        def visit_EBinOp(self, e1, e2):
            if not isinstance(e2, syntax.EBinOp):
                return False
            return (e1.op == e2.op and
                self.visit(e1.e1, e2.e1) and
                self.visit(e1.e2, e2.e2))
        def visit_EUnaryOp(self, e1, e2):
            if not isinstance(e2, syntax.EUnaryOp):
                return False
            return (e1.op == e2.op and self.visit(e1.e, e2.e))
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
        def visit_EGetField(self, e1, e2):
            if not isinstance(e2, syntax.EGetField):
                return False
            return (e1.f == e2.f and self.visit(e1.e, e2.e))
        def visit_Exp(self, e1, e2):
            raise NotImplementedError("{} alpha-equiv? {}".format(e1, e2))

    return V().visit(e1, e2)
