from collections import OrderedDict

import common
from target_syntax import *
import library
from syntax_tools import all_types

INDENT = "  "

class JavaPrinter(common.Visitor):
    def __init__(self):
        self.statevar_name = ""
        self.types = OrderedDict()

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

    def visit_TNative(self, t):
        return t.name

    def visit_THandle(self, t):
        return self.typename(t)

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

    # def visit_EVar(self, e, out):
    #     return "{} = {};\n".format(out, e.id)

    # def visit_EEnumEntry(self, e, out):
    #     return "{} = {};\n".format(out, e.name)

    # def visit_EBool(self, e, out):
    #     return "{} = {};\n".format(out, "true" if e.val else "false")

    # def visit_ENum(self, e, out):
    #     return "{} = {};\n".format(out, e.val)

    # def visit_ELet(self, e, out):
    #     s = self.visit_SDecl(SDecl(e.id, e.e1))
    #     return s + self.visit(e.e2, out)

    # def visit_EBinOp(self, e, out):
    #     op = e.op
    #     if op == "and": op = "&&"
    #     if op == "or": op = "||"
    #     e1 = e.e1
    #     e2 = e.e2
    #     e1_name = common.fresh_name();
    #     e2_name = common.fresh_name();
    #     return """
    #         {t1} {e1};
    #         {compute_e1}
    #         {t2} {e2};
    #         {compute_e2}
    #         {out} = {e1} {op} {e2};
    #         """.format(
    #             t1=self.visit(e1.type),
    #             t2=self.visit(e2.type),
    #             e1=e1_name,
    #             e2=e2_name,
    #             compute_e1=self.visit(e1, e1_name),
    #             compute_e2=self.visit(e2, e2_name),
    #             op=op,
    #             out=out)
    #     return "({} {} {})".format(self.visit(e.e1), e.op, self.visit(e.e2))

    # def visit_EUnaryOp(self, e, out):
    #     op = e.op
    #     e = e.e
    #     if op == "-":
    #         return self.compute(out, [e], lambda val: "(- {})".format(val))
    #     raise NotImplementedError(e.op)

    # def visit_EGetField(self, e, out):
    #     return self.compute(out, [e.e], lambda val: "{}.{}".format(val, e.f))

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

    # def visit_ECall(self, e, out):
    #     def compile(*args):
    #         if e.func == "HashMapLookup":
    #             return "{}.computeIfAbsent({}, ({} key) -> new {}())".format(
    #                 args[0], args[1],
    #                 self.visit(e.args[0].type.k),
    #                 self.visit(e.args[0].type.v))
    #         elif e.func == "LLInsertAtFront":
    #             return "{}.addFirst({})".format(args[0], args[1])
    #         elif e.func == "LLRemove":
    #             return "{}.remove({})".format(args[0], args[1])
    #         elif e.func == "Iterator":
    #             return "{}.iterator()".format(args[0])
    #         else:
    #             return "{}({})".format(e.func, ",".join(args))
    #             # raise NotImplementedError(e.func)

    #     return self.compute(out, e.args, compile)

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

    # def visit_SNoOp(self, s):
    #     return ""

    # def visit_SCall(self, call):
    #     args = [call.target] + list(call.args)
    #     return self.visit_ECall(ECall(call.func, args), out=None)

    # def visit_SDecl(self, s):
    #     return """
    #         {type} {x};
    #         {do_assign}
    #         """.format(
    #             type=self.visit(s.val.type),
    #             x=s.id,
    #             do_assign=self.visit(SAssign(EVar(s.id).with_type(s.val.type), s.val)))

    # def visit_SAssign(self, s):
    #     if isinstance(s.lhs, EVar):
    #         val = common.fresh_name()
    #         return """
    #             {val_type} {val};
    #             {compute_val}
    #             {out} = {val};
    #             """.format(
    #                 val_type=self.visit(s.lhs.type),
    #                 val=val,
    #                 compute_val=self.visit(s.rhs, val),
    #                 out=s.lhs.id)
    #     elif isinstance(s.lhs, EGetField):
    #         out = common.fresh_name()
    #         val = common.fresh_name()
    #         return """
    #             {out_type} {out};
    #             {compute_out};
    #             {val_type} {val};
    #             {compute_val};
    #             {out}.{field} = {val};
    #             """.format(
    #                 out_type=self.visit(s.lhs.e.type),
    #                 val_type=self.visit(s.rhs.type),
    #                 out=out,
    #                 val=val,
    #                 compute_out=self.visit(s.lhs.e, out),
    #                 compute_val=self.visit(s.rhs, val),
    #                 field=s.lhs.f)
    #     else:
    #         raise Exception("not an lvalue: {}".format(s))

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

class CxxPrinter(JavaPrinter):

    def typename(self, t):
        return self.types[t]

    def is_ptr_type(self, t):
        return isinstance(t, THandle)

    def to_ptr(self, x, t):
        return x if self.is_ptr_type(t) else "&({})".format(x)

    def visit_TNative(self, t, name):
        return "{} {}".format(t.name, name)

    def visit_TInt(self, t, name):
        return "int {}".format(name)

    def visit_TLong(self, t, name):
        return "long {}".format(name)

    def visit_TBool(self, t, name):
        return "bool {}".format(name)

    def visit_TRef(self, t, name):
        return self.visit(t.t, "&{}".format(name))

    def visit_TMaybe(self, t, name):
        return self.visit(t.t, name) if self.is_ptr_type(t.t) else self.visit(t.t, "*{}".format(name))

    def visit_THandle(self, t, name):
        return "{} *{}".format(self.typename(t), name)

    def visit_TNativeMap(self, t, name):
        return "std::map< {}, {} > {}".format(self.visit(t.k, ""), self.visit(t.v, ""), name)

    def visit_TMap(self, t, name):
        return self.visit(t.rep_type(), name)

    def visit_TBag(self, t, name):
        return self.visit(t.rep_type(), name)

    def visit_TRecord(self, t, name):
        return "{} {}".format(self.typename(t), name)

    def visit_TEnum(self, enum, name):
        return "{} {}".format(self.typename(enum), name)

    def visit_TVector(self, t, name):
        return "{}[{}]".format(self.visit(t.t, name), t.n)

    def visit_EVectorGet(self, e, indent=""):
        vsetup, v = self.visit(e.e, indent)
        isetup, i = self.visit(e.i, indent)
        return (vsetup + isetup, "{}[{}]".format(v, i))

    def visit_SForEach(self, for_each, indent):
        id = for_each.id
        iter = for_each.iter
        body = for_each.body
        if isinstance(iter.type, library.TIntrusiveLinkedList):
            return self.visit(iter.type.for_each(id, iter, body), indent)
        raise NotImplementedError()

    def visit_SWhile(self, w, indent):
        cond_setup, cond = self.visit(ENot(w.e), indent+INDENT)
        body = self.visit(w.body, indent=indent+INDENT)
        return "{indent0}for (;;) {{\n{cond_setup}{indent}if ({cond}) break;\n{body}{indent0}}}\n".format(
            indent0=indent,
            indent=indent+INDENT,
            cond_setup=cond_setup,
            cond=cond,
            body=body)

    def visit_str(self, s, indent=""):
        return indent + s + "\n"

    def visit_Query(self, q, indent=""):
        ret_type = q.ret.type
        if isinstance(ret_type, TBag):
            x = EVar(common.fresh_name("x")).with_type(ret_type.t)
            s  = "{indent}template <class F>\n".format(indent=indent)
            s += "{indent}inline void {name} ({args}const F& _callback) {{\n{body}  }}\n\n".format(
                indent=indent,
                type=self.visit(ret_type, ""),
                name=q.name,
                args="".join("{}, ".format(self.visit(t, name)) for name, t in q.args),
                body=self.visit(SForEach(x, q.ret, "_callback({});".format(x.id)), indent=indent+INDENT))
            return s
        else:
            body, out = self.visit(q.ret, indent+INDENT)
            return "{indent}inline {type} {name} ({args}) {{\n{body}    return {out};\n  }}\n\n".format(
                indent=indent,
                type=self.visit(ret_type, ""),
                name=q.name,
                args=", ".join(self.visit(t, name) for name, t in q.args),
                out=out,
                body=body)

    def visit_Op(self, q, indent=""):
        s = "{}inline void {} ({}) {{\n{}  }}\n\n".format(
            indent,
            q.name,
            ", ".join(self.visit(t, name) for name, t in q.args),
            self.visit(q.body, indent+INDENT))
        return s

    def visit_ENull(self, e, indent=""):
        return ("", "NULL")

    def visit_EMapGet(self, e, indent=""):
        if isinstance(e.map.type, library.TNativeMap):
            (smap, emap) = self.visit(e.map, indent)
            (skey, ekey) = self.visit(e.key, indent)
            return (smap + skey, "{}[{}]".format(emap, ekey))
        else:
            return self.visit(e.map.type.get_key(e.map, e.key), indent)

    def visit_SMapUpdate(self, update, indent=""):
        if isinstance(update.map.type, library.TNativeMap):
            msetup, map = self.visit(update.map)
            ksetup, key = self.visit(update.key)
            s = "{indent}{decl} = {map}[{key}];\n".format(
                indent=indent,
                decl=self.visit(TRef(update.val_var.type), update.val_var.id),
                map=map,
                key=key)
            return msetup + ksetup + s + self.visit(update.change, indent)
        else:
            return self.visit(update.map.type.update_key(update.map, update.key, update.val_var, update.change), indent)

    def visit_EVar(self, e, indent=""):
        return ("", e.id)

    def visit_EEnumEntry(self, e, indent=""):
        return ("", e.name)

    def visit_EEnumToInt(self, e, indent=""):
        setup, e = self.visit(e.e, indent)
        return (setup, "reinterpret_cast<int>(" + e + ")")

    def visit_EBoolToInt(self, e, indent=""):
        setup, e = self.visit(e.e, indent)
        return (setup, "(" + e + " ? 1 : 0)")

    def visit_EBinOp(self, e, indent=""):
        op = e.op
        ce1, e1 = self.visit(e.e1, indent)
        ce2, e2 = self.visit(e.e2, indent)
        return (ce1 + ce2, "({e1} {op} {e2})".format(e1=e1, op=op, e2=e2))

    def visit_EUnaryOp(self, e, indent):
        op = e.op
        if op == "the":
            setup, elem = self.visit(e.e.type.find_one(e.e))
            return (setup, self.to_ptr(elem, e.e.type.t))
        ce, ee = self.visit(e.e, indent)
        return (ce, "({op} {ee})".format(op=op, ee=ee))

    def visit_EGetField(self, e, indent=""):
        ce, ee = self.visit(e.e, indent)
        op = "."
        if isinstance(e.e.type, THandle) or isinstance(e.e.type, library.TIntrusiveLinkedList):
            op = "->"
        return (ce, "({ee}{op}{f})".format(ee=ee, op=op, f=e.f))

    def visit_ECall(self, e, indent=""):
        setups, args = zip(*[self.visit(arg) for arg in e.args])
        return ("".join(setups), "{func}({args})".format(func=e.func, args=", ".join(args)))

    def visit_Exp(self, e, indent=""):
        raise NotImplementedError(e)

    def visit_SNoOp(self, s, indent=""):
        return ""

    def visit_SAssign(self, s, indent=""):
        cl, el = self.visit(s.lhs, indent)
        cr, er = self.visit(s.rhs, indent)
        return cl + cr + indent + "{} = {};\n".format(el, er)

    def visit_SDecl(self, s, indent=""):
        cv, ev = self.visit(s.val, indent)
        return cv + indent + "{decl} = {ev};\n".format(decl=self.visit(s.val.type, s.id), ev=ev)

    def visit_SSeq(self, s, indent=""):
        return self.visit(s.s1, indent) + self.visit(s.s2, indent)

    def visit_SIf(self, s, indent=""):
        compute_cond, cond = self.visit(s.cond, indent)
        res = """{compute_cond}{indent}if ({cond}) {{\n{then_branch}{indent}}}""".format(
            indent=indent,
            cond=cond,
            compute_cond=compute_cond,
            then_branch=self.visit(s.then_branch, indent + INDENT))
        if not isinstance(s.else_branch, SNoOp):
            res += "{indent}}} else {{\n{else_branch}{indent}}}".format(
                indent=indent,
                else_branch=self.visit(s.else_branch, indent + INDENT))
        return res + "\n"

    def visit_SCall(self, call, indent=""):
        f = getattr(call.target.type, "implement_{}".format(call.func))
        stm = f(call.target, call.args)
        return self.visit(stm, indent)

    def define_type(self, t, name, indent, intrusive_fields):
        if isinstance(t, TEnum):
            return "{indent}enum {name} {{\n{cases}{indent}}};\n".format(
                indent=indent,
                name=name,
                cases="".join("{indent}{case},\n".format(indent=indent+INDENT, case=case) for case in t.cases))
        elif isinstance(t, THandle):
            fields = [("val", t.value_type)] + intrusive_fields[t]
            return "{indent}struct {name} {{\n{fields}{indent}}};\n".format(
                indent=indent,
                name=name,
                fields="".join("{indent}{field_decl};\n".format(indent=indent+INDENT, field_decl=self.visit(t, f)) for (f, t) in fields))
        elif isinstance(t, TRecord):
            return "{indent}struct {name} {{\n{fields}{indent}}};\n".format(
                indent=indent,
                name=name,
                fields="".join("{indent}{field_decl};\n".format(indent=indent+INDENT, field_decl=self.visit(t, f)) for (f, t) in t.fields))
        else:
            return ""

    def initial_value(self, t):
        if isinstance(t, TBool):
            return "(false)"
        elif isinstance(t, TInt) or isinstance(t, TLong):
            return "(0)"
        elif isinstance(t, TVector):
            return "{{ {} }}".format(", ".join(self.initial_value(t.t) for i in range(t.n)))
        elif isinstance(t, library.TNativeMap):
            return "()"
        elif self.visit(t, "").endswith("*"): # a little hacky
            return "(NULL)"
        else:
            return self.initial_value(t.rep_type())

    def visit_Spec(self, spec):
        s = "#pragma once\n"
        s += "#include <map>\n"
        s += "class {} {{\n".format(spec.name)
        s += "public:\n"

        for name, t in spec.types:
            self.types[t] = name
        handle_types = [t for t in all_types(spec) if isinstance(t, THandle)]
        intrusive_fields = { t: [] for t in handle_types }
        for t in all_types(spec):
            if t not in self.types and type(t) in [THandle, TRecord, TTuple, TEnum]:
                if isinstance(t, THandle):
                    name = "{}Handle".format(common.capitalize(t.statevar))
                else:
                    name = common.fresh_name("Type")
                self.types[t] = name
            if hasattr(t, "intrusive_data"):
                for ht in handle_types:
                    intrusive_fields[ht] += t.intrusive_data(ht)
        for t, name in self.types.items():
            s += self.define_type(t, name, "  ", intrusive_fields)
        s += "protected:\n"
        for name, t in spec.statevars:
            self.statevar_name = name
            s += "{}{};\n".format(INDENT, self.visit(t, name))
        s += "public:\n"
        s += INDENT + "inline {name}() : {inits} {{ }}\n".format(name=spec.name, inits=", ".join("{} {}".format(name, self.initial_value(t)) for (name, t) in spec.statevars))
        s += INDENT + "{name}(const {name}& other) = delete;\n".format(name=spec.name)
        for op in spec.methods:
            s += self.visit(op, INDENT)
        s += "};"
        return s
