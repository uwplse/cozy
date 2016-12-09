from collections import OrderedDict
import json

from cozy import common
from cozy.common import fresh_name
from cozy.target_syntax import *
from cozy import library
from cozy.syntax_tools import all_types, fresh_var, subst

INDENT = "  "

class CxxPrinter(common.Visitor):

    def __init__(self):
        self.types = OrderedDict()
        self.funcs = {}

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
        return "std::unordered_map< {}, {} > {}".format(self.visit(t.k, ""), self.visit(t.v, ""), name)

    def visit_TMap(self, t, name):
        return self.visit(t.rep_type(), name)

    def visit_TBag(self, t, name):
        return self.visit(t.rep_type(), name)

    def visit_TRecord(self, t, name):
        return "{} {}".format(self.typename(t), name)

    def visit_TTuple(self, t, name):
        return "{} {}".format(self.typename(t), name)

    def visit_TEnum(self, enum, name):
        return "{} {}".format(self.typename(enum), name)

    def visit_TVector(self, t, name):
        return "{}[{}]".format(self.visit(t.t, name), t.n)

    def visit_EVectorGet(self, e, indent=""):
        vsetup, v = self.visit(e.e, indent)
        isetup, i = self.visit(e.i, indent)
        return (vsetup + isetup, "{}[{}]".format(v, i))

    def visit_SWhile(self, w, indent):
        cond_setup, cond = self.visit(ENot(w.e), indent+INDENT)
        body = self.visit(w.body, indent=indent+INDENT)
        return "{indent0}for (;;) {{\n{cond_setup}{indent}if ({cond}) break;\n{body}{indent0}}}\n".format(
            indent0=indent,
            indent=indent+INDENT,
            cond_setup=cond_setup,
            cond=cond,
            body=body)

    def visit_SBreak(self, s, indent):
        return "{indent}break;\n".format(indent=indent)

    def visit_str(self, s, indent=""):
        return indent + s + "\n"

    def visit_Query(self, q, indent=""):
        ret_type = q.ret.type
        if isinstance(ret_type, TBag):
            x = EVar(common.fresh_name("x")).with_type(ret_type.t)
            s  = "{indent}template <class F>\n".format(indent=indent)
            s += "{indent}inline void {name} ({args}const F& _callback) const {{\n{body}  }}\n\n".format(
                indent=indent,
                type=self.visit(ret_type, ""),
                name=q.name,
                args="".join("{}, ".format(self.visit(t, name)) for name, t in q.args),
                body=self.visit(SForEach(x, q.ret, "_callback({});".format(x.id)), indent=indent+INDENT))
            return s
        else:
            body, out = self.visit(q.ret, indent+INDENT)
            return "{indent}inline {type} {name} ({args}) const {{\n{body}    return {out};\n  }}\n\n".format(
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

    def visit_EBool(self, e, indent=""):
        return ("", "true" if e.val else "false")

    def visit_EJust(self, e, indent=""):
        if self.is_ptr_type(e.e.type):
            return self.visit(e.e)
        raise NotImplementedError(e.type)

    def visit_EAlterMaybe(self, e, indent=""):
        setup1, ee = self.visit(e.e, indent)
        tmp = fresh_var(e.e.type)
        setup2 = "{indent}{decl} = {val};\n".format(indent=indent, decl=self.visit(tmp.type, tmp.id), val=ee)
        res = fresh_var(e.type)
        setup3 = "{indent}{decl};\n".format(
            indent=indent,
            decl=self.visit(res.type, res.id))
        setup4 = self.visit(SIf(EBinOp(tmp, "==", ENull()), SAssign(res, ENull()), SAssign(res, e.f.apply_to(tmp))), indent=indent)
        return (setup1 + setup2 + setup3 + setup4, res.id)

    def visit_EEmptyList(self, e, indent=""):
        return self.visit(e.type.make_empty(), indent)

    def native_map_get(self, e, default_value, indent=""):
        (smap, emap) = self.visit(e.map, indent)
        (skey, ekey) = self.visit(e.key, indent)
        iterator = fresh_var(TNative("auto"), "map_iterator")
        res = fresh_var(e.type, "lookup_result")
        setup_default = self.visit(default_value(res), indent+INDENT)
        s  = "{indent}{declare_res};\n".format(indent=indent, declare_res=self.visit(res.type, res.id))
        s += smap + skey
        s += "{indent}{declare_iterator}({map}.find({key}));\n".format(
            indent=indent,
            declare_iterator=self.visit(iterator.type, iterator.id),
            map=emap,
            key=ekey)
        s += "{indent0}if ({iterator} == {map}.end()) {{\n{setup_default}{indent0}}} else {{\n{indent}{res} = {iterator}->second;\n{indent0}}}\n".format(
            indent0=indent,
            indent=indent+INDENT,
            iterator=iterator.id,
            res=res.id,
            map=emap,
            setup_default=setup_default)
        return (s, res.id)

    def construct_concrete(self, t, e, out):
        """
        Convert an expression of an abstract type (e.g. TBag) to one of a
        concrete type (e.g. TIntrusiveLinkedList) and write the result into
        lvalue `out`.
        """
        if isinstance(t, library.TIntrusiveLinkedList):
            return t.construct_concrete(e, out)
        elif type(t) in [TBool, TInt, TNative, TMaybe, TLong, TString]:
            return SAssign(out, e)
        raise NotImplementedError(type)

    def state_exp(self, lval):
        if isinstance(lval, EVar):
            return self.state_exps[lval.id]
        elif isinstance(lval, ETupleGet):
            return self.state_exp(lval.e).es[lval.n]
        elif isinstance(lval, EGetField):
            return dict(self.state_exp(lval.e).fields)[lval.f]
        else:
            raise NotImplementedError(repr(lval))

    def visit_EMapGet(self, e, indent=""):
        value_constructor = self.state_exp(e.map).value
        if isinstance(e.map.type, library.TNativeMap):
            return self.native_map_get(
                e,
                lambda out: self.construct_concrete(
                    e.map.type.v,
                    value_constructor.apply_to(EEmptyList().with_type(value_constructor.arg.type)),
                    out),
                indent)
        else:
            return self.visit(e.map.type.get_key(e.map, e.key), indent)

    def visit_SMapUpdate(self, update, indent=""):
        if isinstance(update.change, SNoOp):
            return ""
        if isinstance(update.map.type, library.TNativeMap):
            msetup, map = self.visit(update.map, indent)
            ksetup, key = self.visit(update.key, indent)
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

    def visit_ENum(self, e, indent=""):
        return ("", str(e.val))

    def visit_EEnumToInt(self, e, indent=""):
        setup, e = self.visit(e.e, indent)
        return (setup, "static_cast<int>(" + e + ")")

    def visit_EBoolToInt(self, e, indent=""):
        setup, e = self.visit(e.e, indent)
        return (setup, "static_cast<int>(" + e + ")")

    def visit_EBinOp(self, e, indent=""):
        op = e.op
        if op == "+" and isinstance(e.e1.type, TBag):
            raise NotImplementedError("adding bags: {}".format(e))
        elif op == "in":
            type = TBool()
            res = fresh_var(type, "found")
            x = fresh_var(e.e1.type, "x")
            setup = self.visit(seq([
                SDecl(res.id, EBool(False).with_type(type)),
                SForEach(x, e.e2, SIf(
                    EBinOp(x, "==", e.e1),
                    seq([SAssign(res, EBool(True).with_type(type)), SBreak()]),
                    SNoOp()))]), indent)
            return (setup, res.id)
        elif op == "or":
            return self.visit(ECond(e.e1, EBool(True), e.e2).with_type(TBool()), indent)
        elif op == "and":
            return self.visit(ECond(e.e1, e.e2, EBool(False)).with_type(TBool()), indent)
        ce1, e1 = self.visit(e.e1, indent)
        ce2, e2 = self.visit(e.e2, indent)
        return (ce1 + ce2, "({e1} {op} {e2})".format(e1=e1, op=op, e2=e2))

    def for_each(self, iterable : Exp, body, indent="") -> str:
        """Body is function: exp -> stm"""
        x = fresh_var(iterable.type.t)
        if isinstance(iterable, EEmptyList):
            return ""
        elif isinstance(iterable, EMap):
            return self.for_each(
                iterable.e,
                lambda v: body(iterable.f.apply_to(v)),
                indent=indent)
        elif isinstance(iterable, EFilter):
            return self.for_each(iterable.e, lambda x: SIf(iterable.p.apply_to(x), body(x), SNoOp()), indent=indent)
        elif isinstance(iterable, EBinOp) and iterable.op == "+":
            return self.for_each(iterable.e1, body, indent=indent) + self.for_each(iterable.e2, body, indent=indent)
        elif isinstance(iterable, EFlatten):
            # TODO: properly handle breaks inside body
            # TODO: indents get messed up here
            v = fresh_var(iterable.type.t)
            return self.for_each(iterable.e,
                lambda bag: SForEach(v, bag, body(v)),
                indent=indent)
        elif isinstance(iterable, EFlatMap):
            return self.for_each(EFlatten(EMap(iterable.e, iterable.f).with_type(TBag(iterable.type))).with_type(iterable.type), body, indent)
        else:
            if type(iterable.type) is TBag:
                return self.for_each_native(x, iterable, body(x), indent)
            return self.visit(iterable.type.for_each(x, iterable, body(x)), indent=indent)

    def visit_SForEach(self, for_each, indent):
        id = for_each.id
        iter = for_each.iter
        body = for_each.body
        return self.for_each(iter, lambda x: subst(body, {id.id : x}), indent)

    def find_one(self, iterable, indent=""):
        v = fresh_var(TMaybe(iterable.type.t))
        return ("{decl}{find}".format(
            decl=self.visit(SDecl(v.id, ENull().with_type(v.type)), indent=indent),
            find=self.for_each(iterable, lambda x: seq([SAssign(v, EJust(x)), SBreak()]), indent=indent)), v.id)

    def visit_EUnaryOp(self, e, indent):
        op = e.op
        if op == "the":
            return self.find_one(e.e, indent=indent)
        elif op == "sum":
            type = e.e.type.t
            res = fresh_var(type, "sum")
            x = fresh_var(type, "x")
            setup = self.visit(seq([
                SDecl(res.id, ENum(0).with_type(type)),
                SForEach(x, e.e, SAssign(res, EBinOp(res, "+", x)))]), indent)
            return (setup, res.id)
        ce, ee = self.visit(e.e, indent)
        return (ce, "({op} {ee})".format(op=op, ee=ee))

    def visit_EGetField(self, e, indent=""):
        ce, ee = self.visit(e.e, indent)
        op = "."
        if isinstance(e.e.type, THandle) or isinstance(e.e.type, library.TIntrusiveLinkedList):
            op = "->"
        return (ce, "({ee}{op}{f})".format(ee=ee, op=op, f=e.f))

    def visit_ETupleGet(self, e, indent=""):
        return self.visit_EGetField(EGetField(e.e, "_{}".format(e.n)), indent)

    def visit_ECall(self, e, indent=""):
        f = self.funcs[e.func]
        if e.args:
            setups, args = zip(*[self.visit(arg, indent) for arg in e.args])
            return ("".join(setups), "({})".format(f.body_string.format(**{ arg: val for (arg, _), val in zip(f.args, args) })))
        else:
            return ("", f.body_string)

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
            res += " else {{\n{else_branch}{indent}}}".format(
                indent=indent,
                else_branch=self.visit(s.else_branch, indent + INDENT))
        return res + "\n"

    def visit_ECond(self, e, indent=""):
        v = fresh_var(e.type)
        return (
            "{indent}{decl};\n".format(indent=indent, decl=self.visit(v.type, v.id)) +
            self.visit(SIf(e.cond, SAssign(v, e.then_branch), SAssign(v, e.else_branch)), indent),
            v.id)

    def visit_SCall(self, call, indent=""):
        f = getattr(call.target.type, "implement_{}".format(call.func))
        stm = f(call.target, call.args)
        return self.visit(stm, indent)

    def define_type(self, toplevel_name, t, name, indent, sharing):
        if isinstance(t, TEnum):
            return "{indent}enum {name} {{\n{cases}{indent}}};\n".format(
                indent=indent,
                name=name,
                cases="".join("{indent}{case},\n".format(indent=indent+INDENT, case=case) for case in t.cases))
        elif isinstance(t, THandle):
            fields = [("val", t.value_type)]
            s = "{indent}struct {name} {{\n".format(indent=indent, name=name)
            s += "{indent}public:\n".format(indent=indent)
            for (f, ft) in fields:
                s += "{indent}{field_decl};\n".format(indent=indent+INDENT, field_decl=self.visit(ft, f))
            s += "{indent}private:\n".format(indent=indent)
            s += "{indent}friend class {toplevel_name};\n".format(indent=indent+INDENT, toplevel_name=toplevel_name)
            for group in sharing.get(t, []):
                s += "{indent}union {{\n".format(indent=indent+INDENT)
                for gt in group:
                    intrusive_data = gt.intrusive_data(t)
                    s += "{indent}struct {{\n".format(indent=indent+INDENT*2)
                    for (f, ft) in intrusive_data:
                        s += "{indent}{field_decl};\n".format(indent=indent+INDENT*3, field_decl=self.visit(ft, f))
                    s += "{indent}}};\n".format(indent=indent+INDENT*2)
                s += "{indent}}};\n".format(indent=indent+INDENT)
            s += "{indent}}};\n".format(indent=indent)
            return s
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

    def setup_types(self, spec, state_exps, sharing):
        self.types.clear()
        for name, t in spec.types:
            self.types[t] = name
        handle_types = [t for t in all_types(spec) if isinstance(t, THandle)]
        for t in all_types(spec):
            if t not in self.types and type(t) in [THandle, TRecord, TTuple, TEnum]:
                if isinstance(t, THandle):
                    name = "{}Handle".format(common.capitalize(t.statevar))
                else:
                    name = common.fresh_name("Type")
                self.types[t] = name

    def visit_Spec(self, spec, state_exps, sharing):
        self.state_exps = state_exps
        self.funcs = { f.name: f for f in spec.extern_funcs }

        s = "#pragma once\n"
        s += "#include <unordered_map>\n"
        s += "class {} {{\n".format(spec.name)
        s += "public:\n"

        self.setup_types(spec, state_exps, sharing)
        for t, name in self.types.items():
            s += self.define_type(spec.name, t, name, INDENT, sharing)
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

class JavaPrinter(CxxPrinter):

    def visit_Spec(self, spec, state_exps, sharing, package=None):
        self.state_exps = state_exps
        self.funcs = { f.name: f for f in spec.extern_funcs }
        self.setup_types(spec, state_exps, sharing)

        s = ""
        if package:
            s += "package {};\n\n".format(package)

        s += "public class {} implements java.io.Serializable {{\n".format(spec.name)
        for name, t in spec.types:
            self.types[t] = name
        for name, t in spec.statevars:
            s += "{}protected {};\n".format(INDENT, self.visit(t, name))
        for op in spec.methods:
            s += str(self.visit(op, INDENT))

        # generate auxiliary types
        for t, name in self.types.items():
            s += self.define_type(spec.name, t, name, INDENT, sharing)

        s += "}"
        return s

    def visit_Op(self, q, indent=""):
        s = "{}public void {} ({}) {{\n{}  }}\n\n".format(
            indent,
            q.name,
            ", ".join(self.visit(t, name) for name, t in q.args),
            self.visit(q.body, indent+INDENT))
        return s

    def visit_Query(self, q, indent=""):
        ret_type = q.ret.type
        if isinstance(ret_type, TBag):
            x = EVar(common.fresh_name("x")).with_type(ret_type.t)
            def body(x):
                setup, arg = self.visit(x, indent+INDENT*2)
                return setup + "_callback.accept({});".format(arg)
            return "{indent}public void {name} ({args}java.util.function.Consumer<{t}> _callback) {{\n{body}  }}\n\n".format(
                indent=indent,
                type=self.visit(ret_type, ""),
                name=q.name,
                args="".join("{}, ".format(self.visit(t, name)) for name, t in q.args),
                t=self.visit(ret_type.t, ""),
                body=self.for_each(q.ret, body, indent=indent+INDENT))
        else:
            body, out = self.visit(q.ret, indent+INDENT)
            return "{indent}public {type} {name} ({args}) {{\n{body}    return {out};\n  }}\n\n".format(
                indent=indent,
                type=self.visit(ret_type, ""),
                name=q.name,
                args=", ".join(self.visit(t, name) for name, t in q.args),
                out=out,
                body=body)

    def visit_EMakeRecord(self, e, indent=""):
        setups, args = zip(*[self.visit(v, indent) for (f, v) in e.fields])
        tname = self.typename(e.type)
        return ("".join(setups), "new {}({})".format(tname, ", ".join(args)))

    def visit_ENull(self, e, indent=""):
        return ("", "null")

    def visit_EStr(self, e, indent=""):
        return ("", json.dumps(e.val))

    def visit_ENum(self, e, indent=""):
        suffix = ""
        if e.type == TLong():
            suffix = "L"
        return ("", str(e.val) + suffix)

    def visit_EEnumEntry(self, e, indent=""):
        return ("", "{}.{}".format(self.typename(e.type), e.name))

    def visit_EUnaryOp(self, e, indent):
        if e.op == "not":
            setup, ee = self.visit(e.e, indent)
            return (setup, "!({})".format(ee))
        return super().visit_EUnaryOp(e, indent)

    def visit_EBinOp(self, e, indent):
        if e.op == "==":
            setup1, e1 = self.visit(e.e1, indent)
            setup2, e2 = self.visit(e.e2, indent)
            if e1 == "null" or e2 == "null":
                return (setup1 + setup2, "({} == {})".format(e1, e2))
            return (setup1 + setup2, "java.util.Objects.equals({}, {})".format(e1, e2))
        return super().visit_EBinOp(e, indent)

    def define_type(self, toplevel_name, t, name, indent, sharing):
        if isinstance(t, TEnum):
            return "{indent}public enum {name} {{\n{cases}{indent}}}\n".format(
                indent=indent,
                name=name,
                cases="".join("{indent}{case},\n".format(indent=indent+INDENT, case=case) for case in t.cases))
        elif isinstance(t, THandle) or isinstance(t, TRecord):
            public_fields = []
            private_fields = []
            value_equality = True
            if isinstance(t, THandle):
                public_fields = [("val", t.value_type)]
                value_equality = False
                for group in sharing.get(t, []):
                    for gt in group:
                        intrusive_data = gt.intrusive_data(t)
                        for (f, ft) in intrusive_data:
                            private_fields.append((f, ft))
            else:
                public_fields = list(t.fields)
            all_fields = public_fields + private_fields
            s = "{indent}public static final class {name} implements java.io.Serializable {{\n".format(indent=indent, name=name)
            for (f, ft) in public_fields + private_fields:
                s += "{indent}private {field_decl};\n".format(indent=indent+INDENT, field_decl=self.visit(ft, f))
            for (f, ft) in public_fields:
                s += "{indent}public {type} get{Field}() {{ return {field}; }}\n".format(
                    indent=indent+INDENT,
                    type=self.visit(ft, ""),
                    Field=common.capitalize(f),
                    field=f)

            s += "{indent}public {ctor}({args}) {{\n{inits}{indent}}}\n".format(
                indent=indent+INDENT,
                ctor=name,
                args=", ".join(self.visit(ft, f) for (f, ft) in public_fields),
                inits="".join("{indent}this.{f} = {f};\n".format(indent=indent+INDENT*2, f=f) for (f, ft) in public_fields))

            if value_equality:
                hc = fresh_name("hash_code")
                s += "{indent}@Override\n{indent}public int hashCode() {{\n".format(indent=indent+INDENT)
                s += "{indent}int {hc} = 0;\n".format(indent=indent+INDENT*2, hc=hc)
                for (f, ft) in public_fields + private_fields:
                    s += "{indent}{hc} = ({hc} * 31) ^ {f}.hashCode();\n".format(indent=indent+INDENT*2, hc=hc, f=f)
                s += "{indent}return {hc};\n".format(indent=indent+INDENT*2, hc=hc)
                s += "{indent}}}\n".format(indent=indent+INDENT)

                s += "{indent}@Override\n{indent}public boolean equals(Object other) {{\n".format(indent=indent+INDENT)
                s += "{indent}if (other == null) return false;\n".format(indent=indent+INDENT*2)
                s += "{indent}if (other == this) return true;\n".format(indent=indent+INDENT*2)
                s += "{indent}if (!(other instanceof {name})) return false;\n".format(indent=indent+INDENT*2, name=name)
                s += "{indent}{name} o = ({name})other;\n".format(indent=indent+INDENT*2, name=name)
                s += "{indent}return {conds};\n".format(
                    indent=indent+INDENT*2,
                    conds=" && ".join("java.util.Objects.equals(this.{f}, o.{f})".format(f=f) for (f, ft) in all_fields) if all_fields else "true")
                s += "{indent}}}\n".format(indent=indent+INDENT)

            s += "{indent}}}\n".format(indent=indent)
            return s
        elif isinstance(t, TTuple):
            return self.define_type(toplevel_name, TRecord(tuple(("_{}".format(i), t.ts[i]) for i in range(len(t.ts)))), name, indent, sharing);
        else:
            return ""

    def visit_TBool(self, t, name):
        return "Boolean {}".format(name)

    def visit_TInt(self, t, name):
        return "Integer {}".format(name)

    def visit_TLong(self, t, name):
        return "Long {}".format(name)

    def visit_THandle(self, t, name):
        return "{} {}".format(self.typename(t), name)

    def visit_TString(self, t, name):
        return "String {}".format(name)

    def visit_TLinkedList(self, t, name):
        return "java.util.LinkedList<{}> {}".format(self.visit(t.t, ""), name)

    def visit_TArrayList(self, t, name):
        return "java.util.ArrayList<{}> {}".format(self.visit(t.t, ""), name)

    def visit_TBag(self, t, name):
        if hasattr(t, "rep_type"):
            return self.visit(t.rep_type(), name)
        return "java.util.Collection<{}> {}".format(self.visit(t.t, ""), name)

    def visit_SCall(self, call, indent=""):
        if isinstance(call.target.type, library.TLinkedList) or isinstance(call.target.type, library.TArrayList) or type(call.target.type) == TBag:
            if call.func == "add":
                setup1, target = self.visit(call.target, indent)
                setup2, arg = self.visit(call.args[0], indent)
                return setup1 + setup2 + "{}{}.add({});\n".format(indent, target, arg)
            elif call.func == "remove":
                setup1, target = self.visit(call.target, indent)
                setup2, arg = self.visit(call.args[0], indent)
                return setup1 + setup2 + "{}{}.remove({});\n".format(indent, target, arg)
            else:
                raise NotImplementedError(call.func)
        return super().visit_SCall(call, indent)

    def visit_EJust(self, e, indent):
        return self.visit(e.e)

    def visit_EGetField(self, e, indent):
        setup, ee = self.visit(e.e, indent)
        return (setup, "({}).{}".format(ee, e.f))

    def for_each_native(self, x, iterable, body, indent):
        setup, iterable = self.visit(iterable, indent)
        return "{setup}{indent}for ({decl} : {iterable}) {{\n{body}{indent}}}\n".format(
            indent=indent,
            setup=setup,
            decl=self.visit(x.type, x.id),
            iterable=iterable,
            body=self.visit(body, indent+INDENT))

    def find_one_native(self, iterable, indent):
        it = fresh_name("iterator")
        setup, e = self.visit(iterable, indent)
        return (
            "{setup}{indent}{decl} = {e}.iterator();\n".format(
                setup=setup,
                indent=indent,
                decl=self.visit(TNative("java.util.Iterator<>"), it),
                e=e),
            "({it}.hasNext() ? {it}.next() : null)".format(it=it))

    def visit_TNativeMap(self, t, name):
        return "java.util.HashMap<{}, {}> {}".format(
            self.visit(t.k, ""),
            self.visit(t.v, ""),
            name)

    def visit_TMaybe(self, t, name):
        return self.visit(t.t, name)

    def visit_TRef(self, t, name):
        return self.visit(t.t, name)

    def visit_SMapUpdate(self, update, indent=""):
        if isinstance(update.change, SNoOp):
            return ""
        if isinstance(update.map.type, library.TNativeMap):
            vsetup, val = self.visit(EMapGet(update.map, update.key), indent)
            s = "{indent}{decl} = {val};\n".format(
                indent=indent,
                decl=self.visit(TRef(update.val_var.type), update.val_var.id),
                val=val)
            msetup, map = self.visit(update.map, indent) # TODO: deduplicate
            ksetup, key = self.visit(update.key, indent) # TODO: deduplicate
            return vsetup + s + self.visit(update.change, indent) + msetup + "{indent}{map}.put({key}, {val});\n".format(indent=indent, map=map, key=key, val=update.val_var.id)
        else:
            return super().visit_SMapUpdate(update, indent)

    def native_map_get(self, e, default_value, indent=""):
        (smap, emap) = self.visit(e.map, indent)
        (skey, ekey) = self.visit(e.key, indent)
        (sdefault, edefault) = self.visit(default_value, indent)
        return (smap + skey + sdefault, "{emap}.getOrDefault({ekey}, {edefault})".format(emap=emap, ekey=ekey, edefault=edefault))

    def visit_object(self, o, *args, **kwargs):
        return "/* implement visit_{} */".format(type(o).__name__)
