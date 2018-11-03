import itertools
import re

from cozy import common, evaluation
from cozy.target_syntax import *
from cozy.syntax_tools import free_vars, subst, all_exps
from cozy.typecheck import is_scalar, is_collection

from .cxx import CxxPrinter
from .misc import *
from .optimization import simplify_and_optimize

JAVA_PRIMITIVE_TYPES = {
    "boolean", "byte", "char", "short", "int", "long", "float", "double"}

class JavaPrinter(CxxPrinter):

    def __init__(self, out, boxed : bool = True):
        super().__init__(out=out)
        self.boxed = boxed

    def visit_Spec(self, spec, state_exps, sharing, abstract_state=()):
        self.state_exps = state_exps
        self.funcs = { f.name: f for f in spec.extern_funcs }
        self.queries = { q.name: q for q in spec.methods if isinstance(q, Query) }
        self.vars = set(e.id for e in all_exps(spec) if isinstance(e, EVar))
        self.setup_types(spec, state_exps, sharing)

        if spec.header:
            self.write(spec.header.strip() + "\n\n")

        if spec.docstring:
            self.write(spec.docstring + "\n")

        self.write("public class {} implements java.io.Serializable ".format(spec.name))
        with self.block():

            for name, t in spec.types:
                self.types[t] = name

            # member variables
            for name, t in spec.statevars:
                self.write("{}protected {};\n".format(INDENT, self.visit(t, name)))

            # constructor
            self.write(
                "{indent}public {name}() {{\n{indent2}clear();\n{indent}}}\n\n"
                .format(indent=INDENT, indent2=INDENT+INDENT, name=spec.name))

            # explicit constructor
            if abstract_state:
                self.begin_statement()
                self.write("public ", spec.name, "(")
                self.visit_args(abstract_state)
                self.write(") ")
                with self.block():
                    for name, t in spec.statevars:
                        initial_value = state_exps[name]
                        self.visit(simplify_and_optimize(SAssign(EVar(name).with_type(t), initial_value)))
                self.end_statement()

            # clear
            self.begin_statement()
            self.write("public void clear() ")
            with self.block():
                for name, t in spec.statevars:
                    initial_value = state_exps[name]
                    fvs = free_vars(initial_value)
                    initial_value = subst(initial_value,
                        {v.id : evaluation.construct_value(v.type) for v in fvs})
                    setup = simplify_and_optimize(SAssign(EVar(name).with_type(t), initial_value))
                    self.visit(setup)
            self.end_statement()

            # methods
            for op in spec.methods:
                self.visit(op)

            # generate auxiliary types
            for t, name in self.types.items():
                self.define_type(spec.name, t, name, sharing)

        self.write("\n")
        self.write(spec.footer)
        if not spec.footer.endswith("\n"):
            self.write("\n")

    def visit_Op(self, q):
        if q.docstring:
            self.write(indent_lines(q.docstring, self.get_indent()), "\n")
        self.begin_statement()
        self.write("public void ", q.name, "(")
        self.visit_args(q.args)
        self.write(") ")
        with self.block():
            self.visit(simplify_and_optimize(q.body))
        self.end_statement()

    def visit_Query(self, q):
        if q.visibility != Visibility.Public:
            return ""
        ret_type = q.ret.type
        if is_collection(ret_type):
            x = EVar(self.fn("x")).with_type(ret_type.elem_type)
            def body(x):
                return SEscape("{indent}_callback.accept({x});\n", ["x"], [x])
            if q.docstring:
                self.write(indent_lines(q.docstring, self.get_indent()), "\n")
            self.begin_statement()
            self.write("public ", self.visit(TNative("void"), q.name), "(")
            self.visit_args(itertools.chain(q.args, [("_callback", TNative("java.util.function.Consumer<{t}>".format(t=self.visit(ret_type.elem_type, ""))))]))
            self.write(") ")
            with self.block():
                self.visit(simplify_and_optimize(SForEach(x, q.ret, SEscape("{indent}_callback.accept({x});\n", ["x"], [x]))))
        else:
            if q.docstring:
                self.write(indent_lines(q.docstring, self.get_indent()), "\n")
            self.begin_statement()
            self.write("public ", self.visit(ret_type, q.name), "(")
            self.visit_args(q.args)
            self.write(") ")
            with self.block():
                self.visit(simplify_and_optimize(SReturn(q.ret)))
        self.end_statement()

    def visit_EEmptyList(self, e):
        t = self.visit(e.type, "()")
        return "new " + t

    def visit_EEmptyMap(self, e):
        map_type = e.type
        if self.use_trove(map_type):
            if self.trovename(map_type.k) == "Object":
                args = "64, 0.5f, {default}"
            elif self.trovename(map_type.v) == "Object":
                args = "64, 0.5f"
            else:
                args = "64, 0.5f, 0, {default}"
            # args:
            # int initialCapacity, float loadFactor, K noEntryKey, V noEntryValue
            # loadFactor of 0.5 (trove's default) means map has 2x more buckets than entries
            init = "new {}({})".format(self.visit(map_type, name=""), args)
            return self.visit(EEscape(init, ["default"], [evaluation.construct_value(map_type.v)]))
        else:
            return "new {}".format(self.visit(map_type, name="()"))

    def visit_ESingleton(self, e):
        elem = self.visit(e.e)
        v = self.fv(e.type, "singleton")
        self.declare(v, EEmptyList().with_type(e.type))
        self.write_stmt(v.id, ".add(", elem, ");")
        return v.id

    def strip_generics(self, t : str):
        return re.sub("<.*>", "", t)

    def div_by_64_and_round_up(self, e):
        return EBinOp(EBinOp(EBinOp(e, "-", ONE).with_type(INT), ">>", ENum(6).with_type(INT)).with_type(INT), "+", ONE).with_type(INT)

    def initialize_array(self, elem_type, len, out):
        if elem_type == BOOL:
            return SEscape("{indent}{out} = new long[{len}];\n", ["out", "len"], [out, self.div_by_64_and_round_up(len)])
        return SEscape("{indent}{out} = new " + self.strip_generics(self.visit(elem_type, name="")) + "[{len}];\n", ["out", "len"], [out, len])

    def visit_SEscapableBlock(self, s):
        self.begin_statement()
        self.write(s.label, ": do ")
        with self.block():
            self.visit(s.body)
        self.write(" while (false);")
        self.end_statement()

    def visit_SEscapeBlock(self, s):
        self.begin_statement()
        self.write("break ", s.label, ";")
        self.end_statement()

    def visit_EMakeRecord(self, e):
        args = [self.visit(v) for (f, v) in e.fields]
        tname = self.typename(e.type)
        return "new {}({})".format(tname, ", ".join(args))

    def visit_ETuple(self, e):
        name = self.typename(e.type)
        args = [self.visit(arg) for arg in e.es]
        return "new {}({})".format(name, ", ".join(args))

    def visit_ENull(self, e):
        return "null"

    def visit_ENum(self, e):
        suffix = ""
        val = e.val
        if e.type == LONG:
            suffix = "L"
        if e.type == FLOAT:
            val = float(e.val)
            suffix = "f"
        return repr(e.val) + suffix

    def visit_EEnumEntry(self, e):
        return "{}.{}".format(self.typename(e.type), e.name)

    def visit_ENative(self, e):
        assert e.e == ENum(0), "cannot generate code for non-trivial native value"
        return {
            "boolean": "false",
            "byte":    "(byte)0",
            "char":    "'\\0'",
            "short":   "(short)0",
            "int":     "0",
            "long":    "0L",
            "float":   "0.0f",
            "double":  "0.0",
            }.get(e.type.name.strip(), "null")

    def visit_EMove(self, e):
        return self.visit(e.e)

    def _eq(self, e1, e2):
        if not self.boxed and self.is_primitive(e1.type):
            return self.visit(EEscape("({e1} == {e2})", ("e1", "e2"), (e1, e2)).with_type(BOOL))
        if is_scalar(e1.type):
            return self.visit(EEscape("java.util.Objects.equals({e1}, {e2})", ["e1", "e2"], [e1, e2]).with_type(BOOL))
        return super()._eq(e1, e2)

    def test_set_containment_native(self, set : Exp, elem : Exp) -> (str, str):
        return self.visit(EEscape("{set}.contains({elem})", ["set", "elem"], [set, elem]).with_type(BOOL))

    def compute_hash_1(self, e : str, t : Type, out : EVar, indent : str) -> str:
        if self.is_primitive(t) and not self.boxed:
            if t == INT:
                res = e
            elif t == LONG:
                res = "((int)({e})) ^ ((int)(({e}) >> 32))".format(e=e)
            elif t == BOOL:
                res = "({e}) ? 1 : 0".format(e=e)
            elif t == FLOAT:
                res = "Float.floatToIntBits({e})".format(e=e)
            elif isinstance(t, TNative):
                res = {
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

    def compute_hash(self, fields : [(str, Type)]) -> (str, str):
        indent = self.get_indent()
        hc = self.fv(INT, "hash_code")
        s = indent + "int " + hc.id + " = 0;\n"
        for f, ft in fields:
            s += self.compute_hash_1(f, ft, hc, indent)
        return (s, hc.id)

    def define_type(self, toplevel_name, t, name, sharing):
        if isinstance(t, TEnum):
            self.begin_statement()
            self.write("public enum ", name, " ")
            with self.block():
                for case in t.cases:
                    self.begin_statement()
                    self.write(case)
                    self.end_statement()
            self.end_statement()
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
            self.begin_statement()
            self.write("public static class ", name)
            if handle_val_is_this:
                self.write(" extends ", self.visit(t.value_type, ""))
            self.write(" implements java.io.Serializable ")
            with self.block():
                for (f, ft) in public_fields + private_fields:
                    self.begin_statement()
                    self.write("private {field_decl};".format(field_decl=self.visit(ft, f)))
                    self.end_statement()
                for (f, ft) in public_fields:
                    self.begin_statement()
                    self.write("public {type} get{Field}() {{ return {field}; }}".format(
                        type=self.visit(ft, ""),
                        Field=common.capitalize(f),
                        field=f))
                    self.end_statement()
                if handle_val_is_this:
                    self.begin_statement()
                    self.write("public {type} getVal() {{ return this; }}".format(
                        type=self.visit(t.value_type, "")))
                    self.end_statement()

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
                            v = self.fv(ft, "v")
                            args.append((v.id, ft))
                            exps.append(v)
                    return args, exps

                if isinstance(t, THandle):
                    args, exps = flatten([ft for (f, ft) in (t.value_type.fields if handle_val_is_this else public_fields)])
                else:
                    args = public_fields
                    exps = [EVar(f) for (f, ft) in args]
                self.begin_statement()
                self.write("public {ctor}({args}) ".format(ctor=name, args=", ".join(self.visit(ft, f) for (f, ft) in args)))
                with self.block():
                    if handle_val_is_this:
                        es = [self.visit(e) for e in exps]
                        self.begin_statement()
                        self.write("super({args});\n".format(
                            args=", ".join(es)))
                    for ((f, ft), e) in zip(public_fields, exps):
                        e = self.visit(e)
                        self.begin_statement()
                        self.write("this.{f} = {e};\n".format(f=f, e=e))
                self.end_statement()

                if value_equality:
                    self.begin_statement()
                    self.write("@Override")
                    self.end_statement()
                    self.begin_statement()
                    self.write("public int hashCode() ")
                    with self.block():
                        (compute, hc) = self.compute_hash(public_fields + private_fields)
                        self.write(compute)
                        self.begin_statement()
                        self.write("return ", hc, ";")
                        self.end_statement()
                    self.end_statement()

                    self.begin_statement()
                    self.write("@Override")
                    self.end_statement()
                    self.begin_statement()
                    self.write("public boolean equals(Object other) ")
                    with self.block():
                        self.write(self.get_indent(), "if (other == null) return false;\n")
                        self.write(self.get_indent(), "if (other == this) return true;\n")
                        self.write(self.get_indent(), "if (!(other instanceof {name})) return false;\n".format(name=name))
                        self.write(self.get_indent(), "{name} o = ({name})other;\n".format(name=name))
                        eq = self.visit(EAll([EEq(
                            EEscape("this.{}".format(f), (), ()).with_type(ft),
                            EEscape("o.{}".format(f),    (), ()).with_type(ft))
                            for (f, ft) in all_fields]))
                        self.write(self.get_indent(), "return ", eq, ";\n")
                    self.end_statement()
            self.end_statement()
        elif isinstance(t, TTuple):
            return self.define_type(toplevel_name, TRecord(tuple(("_{}".format(i), t.ts[i]) for i in range(len(t.ts)))), name, sharing)
        else:
            return ""

    def visit_TBool(self, t, name):
        return "{} {}".format("Boolean" if self.boxed else "boolean", name)

    def visit_TInt(self, t, name):
        return "{} {}".format("Integer" if self.boxed else "int", name)

    def visit_TLong(self, t, name):
        return "{} {}".format("Long" if self.boxed else "long", name)

    def visit_TFloat(self, t, name):
        return "{} {}".format("Float" if self.boxed else "float", name)

    def is_primitive(self, t):
        return (
            t in {INT, LONG, BOOL, FLOAT} or
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

    def box_if_boolean(self, t : Type) -> Type:
        # See note about boolean collections above.
        return TNative("Boolean") if t == BOOL else t

    def troveargs(self, t):
        if t == BOOL:
            # See note about boolean collections above.
            return "Boolean"
        name = self.trovename(t)
        if name == "Object":
            return self.visit(t, name="")
        return None

    def visit_THandle(self, t, name):
        return "{} {}".format(self.typename(t), name)

    def visit_TString(self, t, name):
        return "String {}".format(name)

    def visit_TList(self, t, name):
        if self.boxed or not self.is_primitive(t.elem_type):
            return "java.util.ArrayList<{}> {}".format(self.visit(t.elem_type, ""), name)
        else:
            return "gnu.trove.list.array.T{}ArrayList {}".format(
                self.trovename(t.elem_type),
                name)

    def visit_TSet(self, t, name):
        if self.boxed or not self.is_primitive(t.elem_type):
            return "java.util.HashSet< {} > {}".format(self.visit(t.elem_type, ""), name)
        else:
            return "gnu.trove.set.hash.T{}HashSet {}".format(
                self.trovename(t.elem_type),
                name)

    def visit_TBag(self, t, name):
        return self.visit_TList(t, name)

    def visit_SCall(self, call):
        target = self.visit(call.target)
        args = [self.visit(a) for a in call.args]
        if type(call.target.type) in (TBag, TSet, TList):
            self.begin_statement()
            if call.func == "add":
                self.write(target, ".add(", args[0], ");")
            elif call.func == "remove":
                self.write(target, ".remove(", args[0], ");")
            else:
                raise NotImplementedError(call.func)
            self.end_statement()
        else:
            raise NotImplementedError(call)

    def visit_EGetField(self, e):
        ee = self.visit(e.e)
        if isinstance(e.e.type, THandle):
            return "({}).getVal()".format(ee, e.field_name)
        return "({}).{}".format(ee, e.field_name)

    def find_one_native(self, iterable):
        it = fresh_name("iterator")
        setup, e = self.visit(iterable)
        return (
            "{setup}{indent}{decl} = {e}.iterator();\n".format(
                setup=setup,
                indent=indent,
                decl=self.visit(TNative("java.util.Iterator<>"), it),
                e=e),
            "({it}.hasNext() ? {it}.next() : null)".format(it=it))

    def visit_TVector(self, t, name):
        return "{}[] {}".format(self.visit(t.elem_type, ""), name)

    def use_trove(self, t):
        if isinstance(t, TMap):
            return not (self.boxed or (not self.is_primitive(t.k) and not self.is_primitive(t.v)))
        return False

    def visit_TArray(self, t, name):
        if t.elem_type == BOOL:
            return "long[] {}".format(name)
        return "{}[] {}".format(self.visit(t.elem_type, name=""), name)

    def visit_TMap(self, t, name):
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
        return self.visit(t.elem_type, name)

    def visit_EMapKeys(self, e):
        m = self.visit(e.e)
        return "({}).keySet()".format(m)

    def visit_SForEach(self, for_each):
        x = for_each.loop_var
        iterable = for_each.iter
        body = for_each.body
        if not self.boxed and self.trovename(x.type) != "Object":
            iterable_src = self.visit(iterable)
            itname = fresh_name("iterator")
            self.write_stmt("gnu.trove.iterator.T{T}Iterator {it} = {iterable}.iterator();".format(
                it=itname,
                iterable=iterable_src,
                T=self.trovename(x.type)))
            self.begin_statement()
            self.write("while ({it}.hasNext()) ".format(it=itname))
            with self.block():
                self.declare(x, EEscape("{it}.next()".format(it=itname), (), ()).with_type(x.type))
                self.visit(body)
            self.end_statement()
            return
        iterable = self.visit(iterable)
        self.begin_statement()
        self.write("for (", self.visit(x.type, x.id), " : ", iterable, ") ")
        with self.block():
            self.visit(body)
        self.end_statement()

    def visit_SSwap(self, s):
        tmp = self.fv(s.lval1.type, "swap_tmp")
        return self.visit(seq([
            SDecl(tmp, s.lval1),
            SAssign(s.lval1, s.lval2),
            SAssign(s.lval2, tmp)]))

    def visit_SMapPut(self, update):
        map = self.visit(update.map)
        key = self.visit(update.key)
        val = self.fv(update.value.type)
        self.declare(val, update.value)
        self.begin_statement()
        self.write(map, ".put(", key, ", ", val.id, ");")
        self.end_statement()

    def visit_SMapUpdate(self, update):
        if isinstance(update.change, SNoOp):
            return ""
        # TODO: liveness analysis to avoid this map lookup in some cases
        self.declare(update.val_var, EMapGet(update.map, update.key).with_type(update.map.type.v))
        map = self.visit(update.map) # TODO: deduplicate
        key = self.visit(update.key) # TODO: deduplicate
        self.visit(update.change)
        self.begin_statement()
        self.write("{map}.put({key}, {val});\n".format(map=map, key=key, val=update.val_var.id))
        self.end_statement()

    def visit_SMapDel(self, update):
        map = self.visit(update.map)
        key = self.visit(update.key)
        self.begin_statement()
        self.write(map, ".remove(", key, ");")
        self.end_statement()

    def visit_SArrayAlloc(self, s):
        self.declare(s.a)
        cap = self.visit(s.capacity)
        elem_type = s.a.type.elem_type
        tname = self.strip_generics(self.visit(elem_type, name=""))
        self.write_stmt(s.a.id, " = new ", tname, "[", cap, "];")

    def visit_SEnsureCapacity(self, s):
        """Ensure that array s.a satisfies capacity requirement s.capacity"""
        return self.array_resize_for_index(s.a.type.elem_type, s.a, EBinOp(s.capacity, "-", ONE).with_type(INT))

    def visit_SArrayReAlloc(self, s):
        return self.array_resize_for_index(s.a.type.elem_type, s.a, s.new_capacity)

    def visit_EArrayIndexOf(self, e):
        # TODO: faster implementation that does not involve this intermediate list?
        # TODO: unboxed version?
        return self.visit(EEscape("java.util.Arrays.asList({a}).indexOf({x})", ("a", "x"), (e.a, e.x)).with_type(e.type))

    def array_resize_for_index(self, elem_type, a, i):
        """Resize the array until `i` is a legal index.

        When i < 0, it will do nothing instead.
        """
        new_a = fresh_name(hint="new_array")
        if elem_type == BOOL:
            t = "long"
        else:
            t = self.strip_generics(self.visit(elem_type, name=""))
        len = EEscape("{a}.length", ["a"], [a]).with_type(INT)
        double_and_incr_size = SEscape(
            "{{indent}}{t}[] {new_a} = new {t}[({{len}} << 1) + 1];\n{{indent}}System.arraycopy({{a}}, 0, {new_a}, 0, {{len}});\n{{indent}}{{a}} = {new_a};\n".format(t=t, new_a=new_a),
            ["a", "len"], [a, len])
        self.visit(SWhile(
            EAll([EBinOp(i, ">=", ZERO).with_type(BOOL), ENot(self.array_in_bounds(elem_type, a, i))]),
            double_and_incr_size))

    def array_put(self, elem_type, a, i, val):
        if elem_type == BOOL:
            return SEscape("{indent}if ({val}) {{ {a}[{i} >> 6] |= (1L << {i}); }} else {{ {a}[{i} >> 6] &= ~(1L << {i}); }};\n",
                ["a", "i", "val"],
                [a, i, val])
        return SEscape("{indent}{lval} = {val};\n", ["lval", "val"], [self.array_get(elem_type, a, i), val])

    def visit_EArrayLen(self, e):
        a = self.visit(e.e)
        return "{}.length".format(a)

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

    def visit_EHasKey(self, e):
        map = self.visit(e.map)
        key = self.visit(e.key)
        return "{map}.containsKey({key})".format(map=map, key=key)

    def visit_EMapGet(self, e):
        if self.use_trove(e.map.type):
            if self.trovename(e.map.type.v) == "Object" and not isinstance(evaluation.construct_value(e.map.type.v), ENull):
                # Le sigh...
                emap = self.visit(e.map)
                ekey = self.visit(e.key)
                v = self.fv(self.box_if_boolean(e.map.type.v), hint="v")
                self.visit(SDecl(v, EEscape("{emap}.get({ekey})".format(emap=emap, ekey=ekey), [], []).with_type(e.type)))
                return self.visit(ECond(EEq(v, ENull().with_type(v.type)), evaluation.construct_value(e.map.type.v), v).with_type(e.type))
            else:
                # For Trove, defaults are set at construction time
                emap = self.visit(e.map)
                ekey = self.visit(e.key)
                return "{emap}.get({ekey})".format(emap=emap, ekey=ekey)
        else:
            emap = self.visit(e.map)
            ekey = self.visit(e.key)
            edefault = self.visit(evaluation.construct_value(e.type))
            return "{emap}.getOrDefault({ekey}, {edefault})".format(emap=emap, ekey=ekey, edefault=edefault)

    def visit(self, x, *args, **kwargs):
        res = super().visit(x, *args, **kwargs)
        if isinstance(res, tuple):
            raise Exception(type(x))
        return res
