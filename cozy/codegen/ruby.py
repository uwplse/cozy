from contextlib import contextmanager

from cozy import evaluation
from cozy.syntax import (
    Query, Visibility,
    Type, INT, BOOL, TTuple, THandle, TRecord, TEnum,
    TBag, TSet, TList,
    Exp, ENum, EVar, ETuple, ETupleGet,
    ENot, EGetField, EEnumEntry,
    SNoOp, SAssign, SDecl, UOp)
from cozy.target_syntax import EMapGet, SReturn
from cozy.syntax_tools import all_exps
from cozy.typecheck import is_scalar

from .cxx import CxxPrinter
from .misc import indent_lines, EEscape, SEscape
from .optimization import simplify_and_optimize


def escape_typename(s):
    if s.startswith("_"):
        return "T" + s
    return s
class RubyPrinter(CxxPrinter):

    def __init__(self, out, boxed : bool = True):
        super().__init__(out=out)
        self.boxed = boxed

    @contextmanager
    def block(self):
        self.end_statement()
        with self.indented():
            yield
        self.begin_statement()


    def visit_args(self, args):
        for (i, (v, t)) in enumerate(args):
            assert isinstance(v, str)
            assert isinstance(t, Type)
            if i > 0:
                self.write(", ")
            self.write(v)

    def visit_SIf(self, s):
        cond = self.visit(s.cond)
        self.begin_statement()
        self.write("if ", cond, "")
        with self.block():
            self.visit(s.then_branch)
        if not isinstance(s.else_branch, SNoOp):
            self.write(" else ")
            with self.block():
                self.visit(s.else_branch)
        self.write("end")
        self.end_statement()

    def visit_Spec(self, spec, state_exps, sharing, abstract_state=()):
        self.state_exps = state_exps
        self.state_vars = [ name for name, t in spec.statevars ]
        self.funcs = { f.name: f for f in spec.extern_funcs }
        self.queries = { q.name: q for q in spec.methods if isinstance(q, Query) }
        self.vars = set(e.id for e in all_exps(spec) if isinstance(e, EVar))
        self.setup_types(spec, state_exps, sharing)

        if spec.header:
            self.write(spec.header.strip() + "\n\n")

        if spec.docstring:
            self.write(spec.docstring + "\n")

        self.write("class {}".format(spec.name))
        with self.block():

            # generate auxiliary types
            for t, name in self.types.items():
                self.define_type(spec.name, t, escape_typename(name), sharing)

            for name, t in spec.types:
                self.types[t] = name

            # explicit constructor
            if abstract_state:
                self.begin_statement()
                self.write("def initialize(")
                self.visit_args(abstract_state)
                self.write(")")
                with self.block():
                    for name, t in spec.statevars:
                        initial_value = state_exps[name]
                        e = simplify_and_optimize(SAssign(EVar("@" + name).with_type(t), initial_value))
                        self.visit(e)
                self.write("end")
                self.end_statement()

            # methods
            for op in spec.methods:
                self.visit(op)

        self.write("\n")
        self.write(spec.footer)
        if not spec.footer.endswith("\n"):
            self.write("\n")
        self.write("end\n")

    def visit_EGetField(self, e):
        ee = self.visit(e.e)
        return "{ee}.{f}".format(ee=ee, f=e.field_name)

    def define_type(self, toplevel_name, t, name, sharing):
        if isinstance(t, TEnum):
            for case in t.cases:
                self.write_stmt(case, " = ", ":" + case)
        elif isinstance(t, THandle) or isinstance(t, TRecord):
            self.begin_statement()
            self.write(name, " = Struct.new(")
            for f, ft in t.fields[:(len(t.fields)-1)]:
                self.write(":", f, ", ")
            self.write(":" + t.fields[-1][0])
            self.write(")")
            self.end_statement()
        elif isinstance(t, TTuple):
            return self.define_type(toplevel_name, TRecord(tuple(("_{}".format(i), t.ts[i]) for i in range(len(t.ts)))), name, sharing)
        else:
            return ""

    def visit_Op(self, q):
        if q.docstring:
            self.write(indent_lines(q.docstring, self.get_indent()), "\n")
        self.begin_statement()
        self.write("def ", q.name, "(")
        self.visit_args(q.args)
        self.write(")")
        with self.block():
            self.visit(simplify_and_optimize(q.body))
        self.write("end")
        self.end_statement()

    def visit_Query(self, q):
        if q.visibility != Visibility.Public:
            return ""
        self.begin_statement()
        self.write("def ", q.name, "(")
        self.visit_args(q.args)
        self.write(")")
        with self.block():
            self.visit(simplify_and_optimize(SReturn(q.ret)))
        self.write("end")
        self.end_statement()

    def visit_EUnaryOp(self, e):
        op = e.op
        if op == UOp.Length:
            ee = self.visit(e.e)
            return "({}.length)".format(ee)
        return super().visit_EUnaryOp(e)

    def visit_EEmptyList(self, e):
        return "[]"

    def visit_EEmptyMap(self, e):
        return "{}"

    def visit_ESingleton(self, e):
        return "[ " + self.visit(e.e) + "]"

    def visit_SEscapableBlock(self, s):
        self.begin_statement()
        self.write("catch :", s.label, " do")
        with self.block():
            self.visit(s.body)
        self.write("end")
        self.end_statement()

    def visit_SEscapeBlock(self, s):
        self.begin_statement()
        self.write("throw :", s.label)
        self.end_statement()

    def visit_SErase(self, s):
        return self.visit(SEscape("{indent}{target}.remove({x})", ("target", "x"), (s.target, s.x)))

    def visit_SInsert(self, s):
        return self.visit(SEscape("{indent}{target}.push({x})", ("target", "x"), (s.target, s.x)))

    def _eq(self, e1, e2):
        if not self.boxed and self.is_primitive(e1.type):
            return self.visit(EEscape("({e1} == {e2})", ("e1", "e2"), (e1, e2)).with_type(BOOL))
        if is_scalar(e1.type):
            return self.visit(EEscape("({e1}.equal? {e2})", ["e1", "e2"], [e1, e2]).with_type(BOOL))
        return super()._eq(e1, e2)

    def test_set_containment_native(self, set : Exp, elem : Exp) -> (str, str):
        return self.visit(EEscape("{set}.include?({elem})", ["set", "elem"], [set, elem]).with_type(BOOL))

    def visit_THandle(self, t, name):
        return name

    def visit_TString(self, t, name):
        return name

    def visit_TList(self, t, name):
        return name

    def visit_TSet(self, t, name):
        return name

    def visit_TBag(self, t, name):
        return self.visit_TList(t, name)

    def visit_TNativeList(self, t, name):
        return name

    def visit_TNativeSet(self, t, name):
        return name

    def visit_TArray(self, t, name):
        return name

    def visit_SReturn(self, ret):
        e = self.visit(ret.e)
        self.write_stmt("return ", e)

    def visit_SCall(self, call):
        target = self.visit(call.target)
        args = [self.visit(a) for a in call.args]
        if type(call.target.type) in (TBag, TSet, TList):
            self.begin_statement()
            if call.func == "add":
                self.write(target, ".push(", args[0], ");")
            elif call.func == "remove":
                self.write(target, ".delete(", args[0], ");")
            else:
                raise NotImplementedError(call.func)
            self.end_statement()
        else:
            raise NotImplementedError(call)

    def visit_TRef(self, t, name):
        return self.visit(t.elem_type, name)

    def visit_EMapKeys(self, e):
        m = self.visit(e.e)
        return "({}).keys".format(m)

    def visit_SForEach(self, for_each):
        x = for_each.loop_var
        iterable = for_each.iter
        body = for_each.body
        iterable = self.visit(iterable)
        self.begin_statement()
        self.write(iterable, ".each do |", x.id , "|")
        with self.block():
            self.visit(body)
        self.write("end")
        self.end_statement()

    def visit_SMapPut(self, update):
        map = self.visit(update.map)
        key = self.visit(update.key)
        val = self.fv(update.value.type)
        self.declare(val, update.value)
        self.begin_statement()
        self.write(map, "[", key, "] = ", val.id)
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
        self.write("{map}[{key}] = {val}\n".format(map=map, key=key, val=update.val_var.id))
        self.end_statement()

    def visit_SMapDel(self, update):
        map = self.visit(update.map)
        key = self.visit(update.key)
        self.begin_statement()
        self.write(map, ".delete(", key, ")")
        self.end_statement()

    def visit_SAssign(self, s):
        value = self.visit(s.rhs)
        self.write_stmt(self.visit(s.lhs), " = ", value)

    def declare(self, v : EVar, initial_value : Exp = None):
        assert hasattr(v, "type"), repr(v)
        if initial_value is not None:
            iv = self.visit(initial_value)
            self.write_stmt(v.id, " = ", iv)

    def visit_EVar(self, e):
        if e.id in self.state_vars:
            return "@" + e.id
        return e.id

    def visit_EHasKey(self, e):
        map = self.visit(e.map)
        key = self.visit(e.key)
        return "{map}.key?({key})".format(map=map, key=key)

    def visit_EMapGet(self, e):
        emap = self.visit(e.map)
        ekey = self.visit(e.key)
        edefault = self.visit(evaluation.construct_value(e.type))
        return "{emap}.fetch({ekey}, {edefault})".format(emap=emap, ekey=ekey, edefault=edefault)

    def visit_EMakeRecord(self, e):
        t = self.visit(e.type, "")
        exps = [ self.visit(ee) for (f, ee) in e.fields ]
        return "({}.new({}))".format(t, ", ".join(exps))

    def visit_ETuple(self, e):
        name = self.typename(e.type)
        args = [self.visit(arg) for arg in e.es]
        return "({}.new({}))".format(name, ", ".join(args))

    def visit_ETupleGet(self, e):
        if isinstance(e.e, ETuple):
            return self.visit(e.e.es[e.index])
        return self.visit_EGetField(EGetField(e.e, "_{}".format(e.index)))

    def visit_SWhile(self, w):
        self.begin_statement()
        self.write("loop do")
        with self.block():
            self.write_stmt("break if ", self.visit(ENot(w.e)))
            self.visit(w.body)
        self.write("end")
        self.end_statement()

    def visit_SSwitch(self, s):
        arg = self.visit(s.e)
        self.begin_statement()
        self.write("case ", arg)
        with self.block():
            for val, body in s.cases:
                assert type(val) in (ENum, EEnumEntry)
                self.write_stmt("when ", self.visit(val))
                with self.indented():
                    self.visit(body)
            self.write_stmt("else")
            with self.indented():
                self.visit(s.default)
        self.write("end")
        self.end_statement()

    def visit_EMove(self, e):
        return self.visit(e.e)

    def visit_SArrayAlloc(self, s):
        a = self.visit(s.a.type, s.a.id)
        cap = self.visit(s.capacity)
        self.write_stmt(a, " = Array.new")

    def visit_EArrayIndexOf(self, e):
        if isinstance(e.a, EVar): pass
        elif isinstance(e.a, ETupleGet) and isinstance(e.a.e, EVar): pass
        else: raise NotImplementedError("finding index of non-var array") # TODO: make this fast when this is false
        res = self.fv(INT, "index")
        self.visit(SDecl(res, EEscape("{a}.index({x})", ("a", "x"), (e.a, e.x)).with_type(INT)))
        return res.id

    def typename(self, t):
        return escape_typename(self.types[t])

    def visit_SEnsureCapacity(self, s):
        pass


    def visit_SSwap(self, s):
        l1 = self.visit(s.lval1)
        l2 = self.visit(s.lval2)
        self.write_stmt(l1, ", ", l2, " = ", l2, ", ", l1)

    def visit_ENull(self, e):
        return "nil"

    def visit_ENative(self, e):
        assert e.e == ENum(0)
        v = self.fv(e.type, "tmp")
        self.write_stmt(self.visit(v), " = ", "nil")
        return v.id
