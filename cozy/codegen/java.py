from contextlib import contextmanager

from cozy import common, library, evaluation
from cozy.target_syntax import *
from cozy.syntax_tools import fresh_var, free_vars, subst, is_scalar

from .cxx import CxxPrinter
from .misc import *

JAVA_PRIMITIVE_TYPES = {
    "boolean", "byte", "char", "short", "int", "long", "float", "double"}

class JavaPrinter(CxxPrinter):

    def __init__(self, boxed : bool = True):
        super().__init__()
        self.boxed = boxed

    @contextmanager
    def boxed_mode(self):
        oldboxed = self.boxed
        self.boxed = True
        yield
        self.boxed = oldboxed

    def visit_Spec(self, spec, state_exps, sharing):
        self.state_exps = state_exps
        self.funcs = { f.name: f for f in spec.extern_funcs }
        self.queries = { q.name: q for q in spec.methods if isinstance(q, Query) }
        self.setup_types(spec, state_exps, sharing)

        s = spec.header
        s += "\npublic class {} implements java.io.Serializable {{\n".format(spec.name)
        for name, t in spec.types:
            self.types[t] = name

        # member variables
        for name, t in spec.statevars:
            s += "{}protected {};\n".format(INDENT, self.visit(t, name))

        # constructor
        s += (
            "{indent}public {name}() {{\n{indent2}clear();\n{indent}}}\n\n"
            .format(indent=INDENT, indent2=INDENT+INDENT, name=spec.name)
        )

        # clear
        s += "{}public void clear() {{\n".format(INDENT, spec.name)
        for name, t in spec.statevars:
            initial_value = state_exps[name]
            fvs = free_vars(initial_value)
            initial_value = subst(initial_value,
                {v.id : evaluation.construct_value(v.type) for v in fvs})
            setup = self.construct_concrete(t, initial_value, EVar(name).with_type(t))
            s += self.visit(setup, INDENT + INDENT)
        s += "{}}}\n\n".format(INDENT)

        # methods
        for op in spec.methods:
            s += str(self.visit(op, INDENT))

        # generate auxiliary types
        for t, name in self.types.items():
            s += self.define_type(spec.name, t, name, INDENT, sharing)

        s += "}\n\n"
        s += spec.footer
        if not s.endswith("\n"):
            s += "\n"
        return s

    def visit_Op(self, q, indent=""):
        s = "{}public void {} ({}) {{\n{}  }}\n\n".format(
            indent,
            q.name,
            ", ".join(self.visit(t, name) for name, t in q.args),
            self.visit(q.body, indent+INDENT))
        return s

    def visit_Query(self, q, indent=""):
        if q.visibility != Visibility.Public:
            return ""
        ret_type = q.ret.type
        if isinstance(ret_type, TBag):
            x = EVar(common.fresh_name("x")).with_type(ret_type.t)
            def body(x):
                return SEscape("{indent}_callback.accept({x});\n", ["x"], [x])
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

    def initialize_native_list(self, out):
        init = "new {};\n".format(self.visit(out.type, name="()"))
        return SEscape("{indent}{e} = " + init, ["e"], [out])

    def initialize_native_set(self, out):
        init = "new {};\n".format(self.visit(out.type, name="()"))
        return SEscape("{indent}{e} = " + init, ["e"], [out])

    def strip_generics(self, t : str):
        import re
        return re.sub("<.*>", "", t)

    def div_by_64_and_round_up(self, e):
        return EBinOp(EBinOp(EBinOp(e, "-", ONE).with_type(INT), ">>", ENum(6).with_type(INT)).with_type(INT), "+", ONE).with_type(INT)

    def initialize_array(self, elem_type, len, out):
        if elem_type == BOOL:
            return SEscape("{indent}{out} = new long[{len}];\n", ["out", "len"], [out, self.div_by_64_and_round_up(len)])
        return SEscape("{indent}{out} = new " + self.strip_generics(self.visit(elem_type, name="")) + "[{len}];\n", ["out", "len"], [out, len])

    def initialize_native_map(self, out):
        if out.type.k == INT:
            return self.initialize_array(out.type.v, ENum(64).with_type(INT), out)
        if self.use_trove(out.type):
            if self.trovename(out.type.k) == "Object":
                args = "64, 0.5f, {default}"
            elif self.trovename(out.type.v) == "Object":
                args = "64, 0.5f"
            else:
                args = "64, 0.5f, 0, {default}"
            # args:
            # int initialCapacity, float loadFactor, K noEntryKey, V noEntryValue
            # loadFactor of 0.5 (trove's default) means map has 2x more buckets than entries
            init = "new {}({});\n".format(self.visit(out.type, name=""), args)
            return SEscape("{indent}{e} = " + init, ["e", "default"], [out, evaluation.construct_value(out.type.v)])
        else:
            init = "new {};\n".format(self.visit(out.type, name="()"))
            return SEscape("{indent}{e} = " + init, ["e"], [out])

    def visit_SEscapableBlock(self, s, indent):
        return "{indent}{label}: do {{\n{body}{indent}}} while (false);\n".format(
            body=self.visit(s.body, indent + INDENT),
            indent=indent,
            label=s.label)

    def visit_SEscapeBlock(self, s, indent):
        return "{indent}break {label};\n".format(indent=indent, label=s.label)

    def visit_EMakeRecord(self, e, indent=""):
        setups, args = zip(*[self.visit(v, indent) for (f, v) in e.fields])
        tname = self.typename(e.type)
        return ("".join(setups), "new {}({})".format(tname, ", ".join(args)))

    def visit_ETuple(self, e, indent=""):
        name = self.typename(e.type)
        setups, args = zip(*[self.visit(arg, indent) for arg in e.es])
        return ("".join(setups), "new {}({})".format(name, ", ".join(args)))

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

    def visit_ENative(self, e, indent=""):
        assert e.e == ENum(0), "cannot generate code for non-trivial native value"
        return ("", {
            "boolean": "false",
            "byte":    "(byte)0",
            "char":    "'\\0'",
            "short":   "(short)0",
            "int":     "0",
            "long":    "0L",
            "float":   "0.0f",
            "double":  "0.0",
            }.get(e.type.name.strip(), "null"))

    def visit_EMove(self, e, indent=""):
        return self.visit(e.e, indent=indent)

    def _eq(self, e1, e2, indent):
        if not self.boxed and self.is_primitive(e1.type):
            return self.visit(EEscape("({e1} == {e2})", ("e1", "e2"), (e1, e2)).with_type(BOOL), indent)
        if (is_scalar(e1.type) or
                (isinstance(e1.type, library.TNativeMap) and isinstance(e2.type, library.TNativeMap)) or
                (isinstance(e1.type, library.TNativeSet) and isinstance(e2.type, library.TNativeSet)) or
                (isinstance(e1.type, library.TNativeList) and isinstance(e2.type, library.TNativeList))):
            return self.visit(EEscape("java.util.Objects.equals({e1}, {e2})", ["e1", "e2"], [e1, e2]).with_type(BOOL), indent)
        return super()._eq(e1, e2, indent)

    def test_set_containment_native(self, set : Exp, elem : Exp, indent) -> (str, str):
        return self.visit(EEscape("{set}.contains({elem})", ["set", "elem"], [set, elem]).with_type(BOOL), indent)

    def compute_hash_1(self, e : str, t : Type, out : EVar, indent : str) -> str:
        if self.is_primitive(t):
            if t == INT:
                res = e
            elif t == LONG:
                res = "((int)({e})) ^ ((int)(({e}) >> 32))".format(e=e)
            elif t == BOOL:
                res = "({e}) ? 1 : 0".format(e=e)
            elif isinstance(t, TNative):
                res =  {
                    "boolean": "{e} ? 1 : 0",
                    "byte":    "{e}",
                    "char":    "{e}",
                    "short":   "{e}",
                    "int":     "{e}",
                    "long":    "((int)({e})) ^ ((int)(({e}) >> 32))",
                    "float":   "Float.floatToIntBits({e})",
                    "double":  "((int)(Double.doubleToRawLongBits({e}))) ^ ((int)((Double.doubleToRawLongBits({e})) >> 32))",
                    }[t.name.strip()].format(e=e)
            else:
                raise NotImplementedError(t)
        else:
            res = "({}).hashCode()".format(e)
        return "{indent}{out} = ({out} * 31) ^ ({res});\n".format(
            indent=indent,
            out=out.id,
            res=res)

    def compute_hash(self, fields : [(str, Type)], indent : str) -> (str, str):
        hc = fresh_var(INT, "hash_code")
        s = indent + "int " + hc.id + " = 0;\n"
        for f, ft in fields:
            s += self.compute_hash_1(f, ft, hc, indent)
        return (s, hc.id)

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
            handle_val_is_this = False
            if isinstance(t, THandle):
                if isinstance(t.value_type, TRecord):
                    handle_val_is_this = True
                else:
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
            s = "{indent}public static class {name}{extends} implements java.io.Serializable {{\n".format(
                indent=indent,
                name=name,
                extends=" extends {}".format(self.visit(t.value_type, "")) if handle_val_is_this else "")
            for (f, ft) in public_fields + private_fields:
                s += "{indent}private {field_decl};\n".format(indent=indent+INDENT, field_decl=self.visit(ft, f))
            for (f, ft) in public_fields:
                s += "{indent}public {type} get{Field}() {{ return {field}; }}\n".format(
                    indent=indent+INDENT,
                    type=self.visit(ft, ""),
                    Field=common.capitalize(f),
                    field=f)
            if handle_val_is_this:
                s += "{indent}public {type} getVal() {{ return this; }}\n".format(
                    indent=indent+INDENT,
                    type=self.visit(t.value_type, ""))

            def flatten(field_types):
                args = []
                exps = []
                for ft in field_types:
                    if isinstance(ft, TRecord):
                        aa, ee = flatten([t for (f, t) in ft.fields])
                        args.extend(aa)
                        exps.append(EMakeRecord(tuple((f, e) for ((f, _), e) in zip(ft.fields, ee))).with_type(ft))
                    elif isinstance(ft, TTuple):
                        aa, ee = flatten(ft.ts)
                        args.extend(aa)
                        exps.append(ETuple(tuple(ee)).with_type(ft))
                    else:
                        v = fresh_var(ft, "v")
                        args.append((v.id, ft))
                        exps.append(v)
                return args, exps

            if isinstance(t, THandle):
                args, exps = flatten([ft for (f, ft) in (t.value_type.fields if handle_val_is_this else public_fields)])
            else:
                args = public_fields
                exps = [EVar(f) for (f, ft) in args]
            s += "{indent}public {ctor}({args}) {{\n".format(indent=indent+INDENT, ctor=name, args=", ".join(self.visit(ft, f) for (f, ft) in args))
            for ((f, ft), e) in zip(public_fields, exps):
                setup, e = self.visit(e, indent=indent+INDENT*2)
                s += setup
                s += "{indent}this.{f} = {e};\n".format(indent=indent+INDENT*2, f=f, e=e)
            if handle_val_is_this:
                setups, es = zip(*[self.visit(e, indent=indent+INDENT*2) for e in exps])
                s += "".join(setups)
                s += "{indent}super({args});\n".format(
                    indent=indent+INDENT*2,
                    args=", ".join(es))
            s += "{indent}}}\n".format(indent=indent+INDENT)

            if value_equality:
                s += "{indent}@Override\n{indent}public int hashCode() {{\n".format(indent=indent+INDENT)
                (compute, hc) = self.compute_hash(public_fields + private_fields, indent=indent+INDENT*2)
                s += compute
                s += "{indent}return {hc};\n".format(indent=indent+INDENT*2, hc=hc)
                s += "{indent}}}\n".format(indent=indent+INDENT)

                s += "{indent}@Override\n{indent}public boolean equals(Object other) {{\n".format(indent=indent+INDENT)
                s += "{indent}if (other == null) return false;\n".format(indent=indent+INDENT*2)
                s += "{indent}if (other == this) return true;\n".format(indent=indent+INDENT*2)
                s += "{indent}if (!(other instanceof {name})) return false;\n".format(indent=indent+INDENT*2, name=name)
                s += "{indent}{name} o = ({name})other;\n".format(indent=indent+INDENT*2, name=name)
                setup, eq = self.visit(EAll([EEq(
                    EEscape("this.{}".format(f), (), ()).with_type(ft),
                    EEscape("o.{}".format(f),    (), ()).with_type(ft))
                    for (f, ft) in all_fields]), indent=indent+INDENT*2)
                s += setup
                s += "{indent}return {cond};\n".format(indent=indent+INDENT*2, cond=eq)
                s += "{indent}}}\n".format(indent=indent+INDENT)

            s += "{indent}}}\n".format(indent=indent)
            return s
        elif isinstance(t, TTuple):
            return self.define_type(toplevel_name, TRecord(tuple(("_{}".format(i), t.ts[i]) for i in range(len(t.ts)))), name, indent, sharing);
        else:
            return ""

    def visit_TBool(self, t, name):
        return "{} {}".format("Boolean" if self.boxed else "boolean", name)

    def visit_TInt(self, t, name):
        return "{} {}".format("Integer" if self.boxed else "int", name)

    def visit_TLong(self, t, name):
        return "{} {}".format("Long" if self.boxed else "int", name)

    def is_primitive(self, t):
        return (
            t in (INT, LONG, BOOL) or
            (isinstance(t, TNative) and t.name.strip() in JAVA_PRIMITIVE_TYPES))

    def trovename(self, t):
        t = common.capitalize(self.visit(t, name="").strip()) if self.is_primitive(t) else "Object"
        if t == "Boolean":
            # Ack! Trove does not support boolean collections. In general, there
            # are more efficient implementations when you only have a finite set
            # of values...
            # See:
            #   https://sourceforge.net/p/trove4j/discussion/121845/thread/1bd4dce9/
            #   https://sourceforge.net/p/trove4j/discussion/121845/thread/ba39ca71/
            return "Object"
        return t

    def troveargs(self, t):
        name = self.trovename(t)
        if name == "Object":
            with self.boxed_mode():
                return self.visit(t, name="")
        return None

    def visit_THandle(self, t, name):
        return "{} {}".format(self.typename(t), name)

    def visit_TString(self, t, name):
        return "String {}".format(name)

    def visit_TNativeList(self, t, name):
        if self.boxed or not self.is_primitive(t.t):
            return "java.util.ArrayList<{}> {}".format(self.visit(t.t, ""), name)
        else:
            return "gnu.trove.list.array.T{}ArrayList {}".format(
                self.trovename(t.t),
                name)

    def visit_TNativeSet(self, t, name):
        if self.boxed or not self.is_primitive(t.t):
            return "java.util.HashSet< {} > {}".format(self.visit(t.t, ""), name)
        else:
            return "gnu.trove.set.hash.T{}HashSet {}".format(
                self.trovename(t.t),
                name)

    def visit_TBag(self, t, name):
        if hasattr(t, "rep_type"):
            return self.visit(t.rep_type(), name)
        return self.visit_TNativeList(t, name)

    def visit_SCall(self, call, indent=""):
        if type(call.target.type) in (library.TNativeList, TBag, library.TNativeSet, TSet):
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

    def visit_EGetField(self, e, indent):
        setup, ee = self.visit(e.e, indent)
        if isinstance(e.e.type, THandle):
            return (setup, "({}).getVal()".format(ee, e.f))
        return (setup, "({}).{}".format(ee, e.f))

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

    def visit_TVector(self, t, name):
        return "{}[] {}".format(self.visit(t.t, ""), name)

    def use_trove(self, t):
        if isinstance(t, TMap):
            return not (self.boxed or (not self.is_primitive(t.k) and not self.is_primitive(t.v)))
        return False

    def visit_TArray(self, t, name):
        if t.t == BOOL:
            return "long[] {}".format(name)
        return "{}[] {}".format(self.visit(t.t, name=""), name)

    def visit_TNativeMap(self, t, name):
        if t.k == INT:
            return self.visit(TArray(t.v), name)
        if self.use_trove(t):
            args = []
            for x in (t.k, t.v):
                x = self.troveargs(x)
                if x is not None:
                    args.append(x)
            return "gnu.trove.map.hash.T{k}{v}HashMap{targs} {name}".format(
                k=self.trovename(t.k),
                v=self.trovename(t.v),
                targs="<{}>".format(", ".join(args)) if args else "",
                name=name)
        else:
            return "java.util.HashMap<{}, {}> {}".format(
                self.visit(t.k, ""),
                self.visit(t.v, ""),
                name)

    def visit_TRef(self, t, name):
        return self.visit(t.t, name)

    def for_each_native(self, x, iterable, body, indent):
        if not self.boxed and self.troveargs(x.type) is None:
            setup, iterable_src = self.visit(iterable, indent)
            itname = fresh_name("iterator")
            return "{setup}{indent}gnu.trove.iterator.T{T}Iterator {it} = {iterable}.iterator();\n{indent}while ({it}.hasNext()) {{\n{indent2}{decl} = {it}.next();\n{body}{indent}}}\n".format(
                setup=setup,
                iterable=iterable_src,
                it=itname,
                T=self.trovename(x.type),
                decl=self.visit(x.type, name=x.id),
                body=self.visit(body, indent+INDENT),
                indent=indent,
                indent2=indent+INDENT)
        return super().for_each_native(x, iterable, body, indent)

    def visit_SMapUpdate(self, update, indent=""):
        if isinstance(update.change, SNoOp):
            return ""
        if isinstance(update.map.type, library.TNativeMap):
            asetup = ""
            if update.map.type.k == INT:
                asetup = self.array_resize_for_index(update.map.type.v, update.map, update.key, indent)
            # TODO: liveness analysis to avoid this map lookup in some cases
            vsetup, val = self.visit(EMapGet(update.map, update.key).with_type(update.map.type.v), indent)
            s = "{indent}{decl} = {val};\n".format(
                indent=indent,
                decl=self.visit(TRef(update.val_var.type), update.val_var.id),
                val=val)
            msetup, map = self.visit(update.map, indent) # TODO: deduplicate
            ksetup, key = self.visit(update.key, indent) # TODO: deduplicate
            if update.map.type.k == INT:
                do_put = self.visit(self.array_put(update.map.type.v, EEscape(map, [], []).with_type(update.map.type), EEscape(key, [], []).with_type(update.key.type), update.val_var), indent)
            else:
                do_put = "{indent}{map}.put({key}, {val});\n".format(indent=indent, map=map, key=key, val=update.val_var.id)
            return asetup + vsetup + s + self.visit(update.change, indent) + msetup + do_put
        else:
            return super().visit_SMapUpdate(update, indent)

    def array_resize_for_index(self, elem_type, a, i, indent):
        new_a = fresh_name(hint="new_array")
        if elem_type == BOOL:
            t = "long"
        else:
            t = self.strip_generics(self.visit(elem_type, name=""))
        len = EEscape("{a}.length", ["a"], [a]).with_type(INT)
        double_size = SEscape(
            "{{indent}}{t}[] {new_a} = new {t}[{{len}} << 1];\n{{indent}}System.arraycopy({{a}}, 0, {new_a}, 0, {{len}});\n{{indent}}{{a}} = {new_a};\n".format(t=t, new_a=new_a),
            ["a", "len"], [a, len])
        return self.visit(SWhile(
            ENot(self.array_in_bounds(elem_type, a, i)),
            double_size), indent)

    def array_put(self, elem_type, a, i, val):
        if elem_type == BOOL:
            return SEscape("{indent}if ({val}) {{ {a}[{i} >> 6] |= (1L << {i}); }} else {{ {a}[{i} >> 6] &= ~(1L << {i}); }};\n",
                ["a", "i", "val"],
                [a, i, val])
        return SEscape("{indent}{lval} = {val};\n", ["lval", "val"], [self.array_get(elem_type, a, i), val])

    def array_get(self, elem_type, a, i):
        if elem_type == BOOL:
            return EEscape("(({a}[{i} >> 6] & (1L << {i})) != 0)", ["a", "i"], [a, i]).with_type(BOOL)
        return EEscape("{a}[{i}]", ["a", "i"], [a, i]).with_type(elem_type)

    def array_in_bounds(self, elem_type, a, i):
        if elem_type == BOOL:
            len = EBinOp(EEscape("{a}.length", ["a"], [a]), "<<", ENum(6).with_type(INT)).with_type(INT)
        else:
            len = EEscape("{a}.length", ["a"], [a]).with_type(INT)
        return EAll([
            EBinOp(i, ">=", ZERO).with_type(BOOL),
            EBinOp(i, "<", len).with_type(BOOL)])

    def native_map_get(self, e, default_value, indent=""):
        if e.key.type == INT:
            return self.visit(ECond(
                self.array_in_bounds(e.map.type.v, e.map, e.key),
                self.array_get(e.map.type.v, e.map, e.key),
                evaluation.construct_value(e.map.type.v)).with_type(e.map.type.v), indent=indent)
        if self.use_trove(e.map.type):
            if self.trovename(e.map.type.v) == "Object" and not isinstance(evaluation.construct_value(e.map.type.v), ENull):
                # Le sigh...
                (smap, emap) = self.visit(e.map, indent)
                (skey, ekey) = self.visit(e.key, indent)
                v = fresh_var(e.map.type.v, hint="v")
                with self.boxed_mode():
                    decl = self.visit(SDecl(v.id, EEscape("{emap}.get({ekey})".format(emap=emap, ekey=ekey), [], []).with_type(e.type)), indent=indent)
                s, e = self.visit(ECond(EEq(v, ENull().with_type(v.type)), evaluation.construct_value(e.map.type.v), v).with_type(e.type), indent=indent)
                return (smap + skey + decl + s, e)
            else:
                # For Trove, defaults are set at construction time
                (smap, emap) = self.visit(e.map, indent)
                (skey, ekey) = self.visit(e.key, indent)
                return (smap + skey, "{emap}.get({ekey})".format(emap=emap, ekey=ekey))
        else:
            (smap, emap) = self.visit(e.map, indent)
            (skey, ekey) = self.visit(e.key, indent)
            edefault = fresh_var(e.type, "lookup_result")
            sdefault = indent + self.visit(edefault.type, edefault.id) + ";\n"
            sdefault += self.visit(default_value(edefault), indent)
            return (smap + skey + sdefault, "{emap}.getOrDefault({ekey}, {edefault})".format(emap=emap, ekey=ekey, edefault=edefault.id))
            # (smap, emap) = self.visit(e.map, indent)
            # (skey, ekey) = self.visit(e.key, indent)
            # edefault = fresh_var(e.type, "default_val")
            # sdefault = indent + self.visit(edefault.type, edefault.id) + ";\n"
            # sdefault += self.visit(default_value(edefault), indent)
            # (srest, res) = self.visit(ECond(
            #     EEscape("{m}.containsKey({k})".format(m=emap, k=ekey), (), ()).with_type(e.type),
            #     EEscape("{m}.get({k})".format(m=emap, k=ekey), (), ()).with_type(e.type),
            #     edefault).with_type(e.type), indent=indent)
            # return (smap + skey + sdefault + srest, res)
            # # return (smap + skey + sdefault, "{emap}.getOrDefault({ekey}, {edefault})".format(emap=emap, ekey=ekey, edefault=edefault.id))

    def visit_object(self, o, *args, **kwargs):
        return "/* implement visit_{} */".format(type(o).__name__)
