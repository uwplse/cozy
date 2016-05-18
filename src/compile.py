import common
from syntax import *

class JavaPrinter(common.Visitor):
    def __init__(self):
        self.statevar_name = ""

    def visit_Spec(self, spec):
        s = "public class {} {{\n".format(spec.name)
        for name, t in spec.types:
            if type(t) == TEnum:
                s += self.visit(t, name, "create")
            elif type(t) == TApp:
                s += self.visit(t, name, "create")
            else:
                s += "{} {}\n".format(self.visit(t), name)
        for name, t in spec.statevars:
            self.statevar_name = name
            s += "  {} {};\n".format(self.visit(t), name)
        for e in spec.assumptions:
            s += "public static boolean assumption {{\n {}\n }}\n\n".format(self.visit(e))
        for op in spec.methods:
            s += str(self.visit(op))
        s += "}"
        return s

    def visit_THandle(self, handle=None, option=None):
        if option == None:
            return "{}".format(self.statevar_name) # hack
        elif option == "initialize":
            return "new {}()".format(self.statevar_name)

    def visit_TEnum(self, enum, name=None, option=None):
        if option == "create":
            return "putlic static enum {} {{\n {} \n}} \n".format(name, ",".join(enum.cases))
        else:
            print("unknown option")

    def visit_TNamed(self, named):
        return named.id

    def visit_TApp(self, app, name=None, option=None):
        if option == "create":
            return "public class {} {{\n {} \n}}\n".format(name, self.visit(app.args))
        elif option == None:
            return "{}<{}>".format(app.t, self.visit(app.args))
        else:
            print("unknown option")

    def visit_TRecord(self, r):
        return "{}".format(", ".join("{} {}".format(self.visit(t), f) for f, t in r.fields))

    def visit_TList(self, l, option=None):
        if option == None:
            return "List<{}>".format(self.visit(l.t))
        elif option == "initialize":
            return "new ArrayList<{}>()".format(self.visit(l.t))

    def visit_TInt(self, i, option=None):
        if option == None:
            return "Integer"
        elif option == "initialize":
            return "0"

    def visit_Query(self, q):
        ret_type = self.visit(q.ret.type)
        s = "public {} {} ({}) {{\n {} result = {};\n {} \n}}\n\n".format(
            ret_type, 
            q.name,
            ", ".join("{} {}".format(self.visit(t), name) for name, t in q.args), 
            ret_type,
            self.visit(q.ret.type, "initialize"),
            self.visit(q.ret))
        return s

    def visit_Op(self, q):
        s = "public void {} ({}) {{\n {} \n}}\n\n".format(q.name, ", ".join("{} {}".format(self.visit(t), name) for name, t in q.args), 
            self.visit(q.body))
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
        s = self.visit(e.e, e.op)
        return s

    def visit_EGetField(self, e):
        s = "({}).{}".format(self.visit(e.e), e.f)
        return s

    def visit_EMakeRecord(self, e):
        return "{{ {} }}".format(", ".join("{} : {}".format(name, val) for name, val in e.fields))

    def visit_EListComprehension(self, e, op=None):
        s = ""
        cpull_clause = ""
        ccond_clause = []
        for clause in e.clauses:
            if type(clause) == CPull:
                cpull_clause += self.visit(clause)
            elif type(clause) == CCond:
                ccond_clause.append(self.visit(clause))
        s += cpull_clause + "{\n"
        for clause in ccond_clause:
            s += (clause + "{\n")

        if op == None:
            s += "{}.add(e);\n".format("result")
        elif op == "sum":
            s += "{} += {};\n".format("result", self.visit(e.e))
        elif op == "some":
            s += "{} = {};\n".format("result", self.visit(e.e))
        elif op == "unique":
            s += "assert unique({});\n".format(self.visit(e.e))
        elif op == "max":
            s += "result = Math.max(result, {});\n".format(self.visit(e.e))
        for clause in ccond_clause:
            s += "}\n"
        s += "}\n"
        return s

    def visit_EAlloc(self, e):
        return "new {}({})".format(self.visit(e.t), ", ".join(self.visit(arg) for arg in e.args))

    def visit_ECall(self, e):
        return "{}({})".format(e.func, ", ".join(self.visit(arg) for arg in e.args))

    def visit_CPull(self, c):
        return "for ({} {}: {})".format(self.visit_THandle(), c.id, self.visit(c.e))

    def visit_CCond(self, c):
        return "if ({})".format(self.visit(c.e))

    def visit_SNoOp(self, s):
        return "()"

    def visit_SCall(self, s):
        return "{}.{}({})".format(s.target, s.func, ", ".join(self.visit(arg) for arg in s.args))

    def visit_SAssign(self, s):
        return "{}.{} = {}".format(self.visit(s.lhs), s.lhs.f, self.visit(s.rhs))

    def visit_SDel(self, s):
        return "{}.remove({})".format(self.statevar_name, self.visit(s.e))





