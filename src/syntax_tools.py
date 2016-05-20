"""
Various utilities for working with syntax trees.

    pprint(ast) -> str            prettyprint a syntax tree

"""

import common
import syntax

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

    def visit_TInt(self, t):
        return "Int"

    def visit_TRecord(self, r):
        return "{{ {} }}".format(", ".join("{} : {}".format(f, self.visit(t)) for f, t in r.fields))

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
        s += "    {}\n".format(self.visit(q.body))
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

    def visit_EListComprehension(self, e):
        return "[{} | {}]".format(self.visit(e.e), ", ".join(self.visit(clause) for clause in e.clauses))

    def visit_EAlloc(self, e):
        return "new {}({})".format(self.visit(e.t), ", ".join(self.visit(arg) for arg in e.args))

    def visit_ECall(self, e):
        return "{}({})".format(e.func, ", ".join(self.visit(arg) for arg in e.args))

    def visit_ETuple(self, e):
        return "({})".format(", ".join(self.visit(e) for e in e.es))

    def visit_CPull(self, c):
        return "{} <- {}".format(c.id, self.visit(c.e))

    def visit_CCond(self, c):
        return self.visit(c.e)

    def visit_SNoOp(self, s):
        return "()"

    def visit_SCall(self, s):
        return "{}.{}({})".format(s.target, s.func, ", ".join(self.visit(arg) for arg in s.args))

    def visit_SAssign(self, s):
        return "{} = {}".format(self.visit(s.lhs), self.visit(s.rhs))

    def visit_SDel(self, s):
        return "del {}".format(self.visit(s.e))


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
                raise Exception("uknown case: {}".format(c))

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

    return Subst().visit(exp)
