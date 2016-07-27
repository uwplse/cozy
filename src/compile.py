import common
from syntax import *

class JavaPrinter(common.Visitor):
    def __init__(self):
        self.statevar_name = ""
        self.types = { }

    def visit_Spec(self, spec):
        s = "public class {} {{\n".format(spec.name)
        for name, t in spec.types:
            self.types[t] = name
        for name, t in spec.statevars:
            self.statevar_name = name
            s += "  {} {};\n".format(self.visit(t), name)
        for e in spec.assumptions:
            s += "public static boolean assumption {{\n {}\n }}\n\n".format(self.visit(e))
        for op in spec.methods:
            s += str(self.visit(op))

        # generate auxiliary types
        seen = set()
        changed = True
        while changed:
            changed = False
            for ty, name in list(self.types.items()):
                if ty not in seen:
                    changed = True
                    seen.add(ty)
                    s += self.gen_type(name, ty)

        s += "}"
        return s

    def gen_type(self, name, ty):
        if isinstance(ty, TEnum):
            s = """
                static enum {name} {{ {cases} }}
                """.format(name=name, cases=",".join(ty.cases))
            for c in ty.cases:
                s += "static final {name} {case} = {name}.{case};\n".format(name=name, case=c)
            return s
        elif isinstance(ty, TRecord):
            return """
                static class {name} {{ {fields} }}
                """.format(name=name, fields="".join("{} {};".format(self.visit(ft), f) for (f,ft) in ty.fields))
        return ""
        # TODO: other types?

    def typename(self, t):
        if isinstance(t, TInt): return "Integer"
        if isinstance(t, TLong): return "Long"
        if isinstance(t, TBool): return "Boolean"
        if isinstance(t, TString): return "String"
        res = self.types.get(t)
        if res is None:
            res = common.fresh_name("Type")
            self.types[t] = res
        return res

    def visit_THandle(self, t):
        return "{}Handle".format(common.capitalize(t.statevar))

    def visit_TEnum(self, enum):
        return self.typename(enum)

    def visit_TNamed(self, named):
        return named.id

    def visit_TApp(self, app, name=None, option=None):
        if option == "create":
            return "public class {} {{\n {} \n}}\n".format(name, self.visit(app.args))
        elif option == None:
            return "{}<{}>".format(app.t, self.visit(app.args))
        else:
            print("unknown option")

    def visit_TLinkedList(self, t):
        return "java.util.LinkedList<{}>".format(self.visit(t.t))

    def visit_THashMap(self, t):
        return "java.util.HashMap<{}, {}>".format(self.visit(t.k), self.visit(t.v))

    def visit_TRecord(self, r):
        return self.typename(TRecord(tuple(r.fields)))

    def visit_TInt(self, t):
        return self.typename(t)

    def visit_TLong(self, t):
        return self.typename(t)

    def visit_TBool(self, t):
        return self.typename(t)

    def visit_TIterator(self, t):
        return "java.util.Iterator<{}>".format(self.visit(t.t))

    def visit_Query(self, q):
        ret_type = self.visit(q.ret.type)
        out_name = common.fresh_name("result")
        s = "public {type} {name} ({args}) {{\n {type} {out}; {body} return {out}; \n}}\n\n".format(
            type=ret_type,
            name=q.name,
            args=", ".join("{} {}".format(self.visit(t), name) for name, t in q.args),
            out=out_name,
            body=self.visit(q.ret, out_name))
        return s

    def visit_Op(self, q):
        s = "public void {} ({}) {{\n {} \n}}\n\n".format(q.name, ", ".join("{} {}".format(self.visit(t), name) for name, t in q.args), 
            self.visit(q.body))
        return s

    def compute(self, out, exps, callback):
        s = ""
        tmps = [common.fresh_name() for e in exps]
        for (tmp, e) in zip(tmps, exps):
            s += "{} {};\n".format(self.visit(e.type), tmp)
            s += self.visit(e, tmp)
        return s + (
            "{} = {};\n".format(out, callback(*tmps)) if out is not None else
            "{};\n".format(callback(*tmps)))

    def visit_EVar(self, e, out):
        return "{} = {};\n".format(out, e.id)

    def visit_EBool(self, e, out):
        return "{} = {};\n".format(out, "true" if e.val else "false")

    def visit_ENum(self, e, out):
        return "{} = {};\n".format(out, e.val)

    def visit_ELet(self, e, out):
        s = self.visit_SDecl(SDecl(e.id, e.e1))
        return s + self.visit(e.e2, out)

    def visit_EBinOp(self, e, out):
        op = e.op
        if op == "and": op = "&&"
        if op == "or": op = "||"
        e1 = e.e1
        e2 = e.e2
        e1_name = common.fresh_name();
        e2_name = common.fresh_name();
        return """
            {t1} {e1};
            {compute_e1}
            {t2} {e2};
            {compute_e2}
            {out} = {e1} {op} {e2};
            """.format(
                t1=self.visit(e1.type),
                t2=self.visit(e2.type),
                e1=e1_name,
                e2=e2_name,
                compute_e1=self.visit(e1, e1_name),
                compute_e2=self.visit(e2, e2_name),
                op=op,
                out=out)
        return "({} {} {})".format(self.visit(e.e1), e.op, self.visit(e.e2))

    def visit_EUnaryOp(self, e, out):
        op = e.op
        e = e.e
        if op == "-":
            return self.compute(out, [e], lambda val: "(- {})".format(val))
        raise NotImplementedError(e.op)

    def visit_EGetField(self, e, out):
        return self.compute(out, [e.e], lambda val: "{}.{}".format(val, e.f))

    # def visit_EMakeRecord(self, e):
    #     return "{{ {} }}".format(", ".join("{} : {}".format(name, val) for name, val in e.fields))

    # def visit_EListComprehension(self, e, op=None):
    #     s = ""
    #     cpull_clause = ""
    #     ccond_clause = []
    #     for clause in e.clauses:
    #         if type(clause) == CPull:
    #             cpull_clause += self.visit(clause)
    #         elif type(clause) == CCond:
    #             ccond_clause.append(self.visit(clause))
    #     s += cpull_clause + "{\n"
    #     for clause in ccond_clause:
    #         s += (clause + "{\n")

    #     if op == None:
    #         s += "{}.add(e);\n".format("result")
    #     elif op == "sum":
    #         s += "{} += {};\n".format("result", self.visit(e.e))
    #     elif op == "some":
    #         s += "{} = {};\n".format("result", self.visit(e.e))
    #     elif op == "unique":
    #         s += "assert unique({});\n".format(self.visit(e.e))
    #     elif op == "max":
    #         s += "result = Math.max(result, {});\n".format(self.visit(e.e))
    #     for clause in ccond_clause:
    #         s += "}\n"
    #     s += "}\n"
    #     return s

    # def visit_EAlloc(self, e):
    #     return "new {}({})".format(self.visit(e.t), ", ".join(self.visit(arg) for arg in e.args))

    def visit_ECall(self, e, out):
        def compile(*args):
            if e.func == "HashMapLookup":
                return "{}.computeIfAbsent({}, ({} key) -> new {}())".format(
                    args[0], args[1],
                    self.visit(e.args[0].type.k),
                    self.visit(e.args[0].type.v))
            elif e.func == "LLInsertAtFront":
                return "{}.addFirst({})".format(args[0], args[1])
            elif e.func == "LLRemove":
                return "{}.remove({})".format(args[0], args[1])
            elif e.func == "Iterator":
                return "{}.iterator()".format(args[0])
            else:
                return "{}({})".format(e.func, ",".join(args))
                # raise NotImplementedError(e.func)

        return self.compute(out, e.args, compile)

        # tmps = [common.fresh_name() for i in range(len(e.args))]
        # s = ""
        # for (tmpname, arg) in zip(tmps, e.args):
        #     s += "{} {};".format(self.visit(arg.type), tmpname);
        #     s += self.visit(arg, tmpname)
        # return s + "{} = {}({});".format(out, e.func, ", ".join(tmps))

    # def visit_CPull(self, c):
    #     return "for ({} {}: {})".format(self.visit_THandle(), c.id, self.visit(c.e))

    # def visit_CCond(self, c):
    #     return "if ({})".format(self.visit(c.e))

    def visit_SNoOp(self, s):
        return ""

    def visit_SCall(self, call):
        args = [call.target] + list(call.args)
        return self.visit_ECall(ECall(call.func, args), out=None)

    def visit_SDecl(self, s):
        return """
            {type} {x};
            {do_assign}
            """.format(
                type=self.visit(s.val.type),
                x=s.x,
                do_assign=self.visit(SAssign(EVar(s.x).with_type(s.val.type), s.val)))

    def visit_SAssign(self, s):
        if isinstance(s.lhs, EVar):
            val = common.fresh_name()
            return """
                {val_type} {val};
                {compute_val}
                {out} = {val};
                """.format(
                    val_type=self.visit(s.lhs.type),
                    val=val,
                    compute_val=self.visit(s.rhs, val),
                    out=s.lhs.id)
        elif isinstance(s.lhs, EGetField):
            out = common.fresh_name()
            val = common.fresh_name()
            return """
                {out_type} {out};
                {compute_out};
                {val_type} {val};
                {compute_val};
                {out}.{field} = {val};
                """.format(
                    out_type=self.visit(s.lhs.e.type),
                    val_type=self.visit(s.rhs.type),
                    out=out,
                    val=val,
                    compute_out=self.visit(s.lhs.e, out),
                    compute_val=self.visit(s.rhs, val),
                    field=s.lhs.f)
        else:
            raise Exception("not an lvalue: {}".format(s))

    def visit_SSeq(self, s):
        return self.visit(s.s1) + self.visit(s.s2)

    def visit_SIf(self, s):
        cond = common.fresh_name("cond");
        return """
            {bool_type} {cond};
            {compute_cond}
            if ({cond}) {{
                {then_branch}
            }} else {{
                {else_branch}
            }}""".format(
                bool_type=self.visit(TBool()),
                cond=cond,
                compute_cond=self.visit(s.cond, cond),
                then_branch=self.visit(s.then_branch),
                else_branch=self.visit(s.else_branch))

    def visit_object(self, o, *args, **kwargs):
        return "/* implement visit_{} */".format(type(o).__name__)
