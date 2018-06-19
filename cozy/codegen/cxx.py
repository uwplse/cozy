from collections import OrderedDict
import json
import itertools
from io import StringIO

from cozy import common, evaluation
from cozy.common import fresh_name, declare_case
from cozy.target_syntax import *
from cozy.syntax_tools import all_types, fresh_var, subst, free_vars, is_scalar, mk_lambda, alpha_equivalent, all_exps, break_seq, is_lvalue
from cozy.typecheck import is_collection, is_numeric
from cozy.structures import extension_handler

from .misc import *

EMove = declare_case(Exp, "EMove", ["e"])
SScoped = declare_case(Stm, "SScoped", ["s"])

class CxxPrinter(CodeGenerator):

    def __init__(self, out, use_qhash : bool = False):
        super().__init__(out=out)
        self.types = OrderedDict()
        self.funcs = {}
        self.queries = {}
        self.use_qhash = use_qhash
        self.vars = set() # set of strings

    def fn(self, hint="var"):
        n = common.fresh_name(hint, omit=self.vars)
        self.vars.add(n)
        return n

    def fv(self, t, hint="var"):
        n = fresh_var(t, hint=hint, omit=self.vars)
        self.vars.add(n.id)
        return n

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

    def visit_TFloat(self, t, name):
        return "float {}".format(name)

    def visit_TBool(self, t, name):
        return "bool {}".format(name)

    def visit_TRef(self, t, name):
        return self.visit(t.t, "&{}".format(name))

    def visit_THandle(self, t, name):
        return "{} *{}".format(self.typename(t), name)

    def visit_TString(self, t, name):
        return "std::string {}".format(name)

    def visit_TNativeMap(self, t, name):
        if self.use_qhash:
            return "QHash< {}, {} > {}".format(self.visit(t.k, ""), self.visit(t.v, ""), name)
        else:
            return "std::unordered_map< {}, {}, {} > {}".format(self.visit(t.k, ""), self.visit(t.v, ""), self._hasher(t.k), name)

    def visit_TMap(self, t, name):
        if type(t) is TMap:
            return self.visit_TNativeMap(t, name)
        return self.visit(t.rep_type(), name)

    def visit_TList(self, t, name):
        if type(t) is TList:
            return self.visit_TNativeList(t, name)
        return self.visit_Type(t, name)

    def visit_TBag(self, t, name):
        if type(t) is TBag:
            return self.visit_TNativeList(t, name)
        return self.visit_Type(t, name)

    def visit_TSet(self, t, name):
        return self.visit_TNativeSet(t, name)

    def visit_TNativeList(self, t, name):
        return "std::vector< {} > {}".format(self.visit(t.t, ""), name)

    def visit_TNativeSet(self, t, name):
        return "std::unordered_set< {}, {} > {}".format(self.visit(t.t, ""), self._hasher(t.t), name)

    def visit_TArray(self, t, name):
        return "std::vector< {} > {}".format(self.visit(t.t, ""), name)

    def visit_Type(self, t, name):
        h = extension_handler(type(t))
        if h is not None:
            return self.visit(h.rep_type(t), name)
        raise NotImplementedError(t)

    def visit_TRecord(self, t, name):
        return "{} {}".format(self.typename(t), name)

    def visit_TTuple(self, t, name):
        return "{} {}".format(self.typename(t), name)

    def visit_TEnum(self, enum, name):
        return "{} {}".format(self.typename(enum), name)

    def visit_ELet(self, e):
        if isinstance(e.e, EVar):
            return self.visit(e.f.apply_to(e.e))
        v = self.fv(e.e.type)
        self.declare(v, e.e)
        return self.visit(e.f.apply_to(v))

    def visit_TVector(self, t, name):
        return "{}[{}]".format(self.visit(t.t, name), t.n)

    def visit_EVectorGet(self, e):
        v = self.visit(e.e)
        i = self.visit(e.i)
        return "{}[{}]".format(v, i)

    def visit_SWhile(self, w):
        self.begin_statement()
        self.write("for (;;) ")
        with self.block():
            self.visit(SIf(ENot(w.e), SEscape("{indent}break;\n", (), ()), SNoOp()))
            self.visit(w.body)
        self.end_statement()

    def visit_SSwap(self, s):
        l1 = self.visit(s.lval1)
        l2 = self.visit(s.lval2)
        self.write_stmt("std::swap(", l1, ", ", l2, ");")

    def visit_SSwitch(self, s):
        arg = self.visit(s.e)
        self.begin_statement()
        self.write("switch (", arg, ") ")
        with self.block():
            for val, body in s.cases:
                assert type(val) in (ENum, EEnumEntry)
                self.write_stmt("case ", self.visit(val), ":")
                with self.indented():
                    self.visit(body)
                    self.write_stmt("break;")
            self.write_stmt("default:")
            with self.indented():
                self.visit(s.default)
        self.end_statement()

    def visit_SEscapableBlock(self, s):
        self.visit(SScoped(s.body))
        self.write(s.label, ":\n")

    def visit_SEscapeBlock(self, s):
        self.begin_statement()
        self.write("goto ", s.label, ";")
        self.end_statement()

    def visit_Query(self, q):
        if q.visibility != Visibility.Public:
            return ""
        ret_exp = q.ret
        ret_type = ret_exp.type
        if is_collection(ret_type):
            x = self.fv(ret_type.t, "x")
            if q.docstring:
                self.write(indent_lines(q.docstring, self.get_indent()), "\n")
            self.begin_statement()
            self.write("template <class F>")
            self.end_statement()
            self.begin_statement()
            self.write("inline void ", q.name, "(")
            self.visit_args(itertools.chain(q.args, [("_callback", TNative("const F&"))]))
            self.write(") ")
            with self.block():
                self.visit(SForEach(x, ret_exp, SEscape("{indent}_callback({x});\n", ["x"], [x])))
            self.end_statement()
        else:
            if q.docstring:
                self.write(indent_lines(q.docstring, self.get_indent()), "\n")
            self.begin_statement()
            self.write("inline ", self.visit(ret_type, ""), " ", q.name, "(")
            self.visit_args(q.args)
            self.write(") ")
            with self.block():
                ret = self.visit(ret_exp)
                self.begin_statement()
                self.write("return ", ret, ";")
                self.end_statement()
            self.end_statement()

    def visit_Op(self, q):
        if q.docstring:
            self.write(indent_lines(q.docstring, self.get_indent()), "\n")
        self.begin_statement()
        self.write("inline void ", q.name, " (")
        self.visit_args(q.args)
        self.write(") ")
        with self.block():
            self.visit(q.body)
        self.end_statement()

    def visit_ENull(self, e):
        return "nullptr"

    def visit_EBool(self, e):
        return "true" if e.val else "false"

    def visit_EEmptyList(self, e):
        v = self.fv(e.type)
        self.declare(v)
        self.visit(self.construct_concrete(e.type, e, v))
        return v.id

    def native_map_get(self, e, default_value):
        emap = self.visit(e.map)
        if self.use_qhash:
            return "{}.value({})".format(emap, ekey)
        t = self.visit(e.map.type, "").strip() + "::const_iterator"
        iterator = self.fv(TNative(t), "map_iterator")
        self.declare(iterator, EEscape(emap + ".find({key})", ("key",), (e.key,)))
        return self.visit(ECond(
            EEscape("{it} == " + emap + ".end()", ("it",), (iterator,)).with_type(BOOL),
            evaluation.construct_value(e.type),
            EEscape("{it}->second", ("it",), (iterator,)).with_type(e.type)).with_type(e.type))

    def to_lvalue(self, e : Exp) -> Exp:
        if is_lvalue(e):
            return e
        v = self.fv(e.type, "x")
        self.declare(v, e)
        return v

    def construct_concrete(self, t : Type, e : Exp, out : Exp):
        """
        Construct a value of type `t` from the expression `e` and store it in
        lvalue `out`.
        """
        if hasattr(t, "construct_concrete"):
            return t.construct_concrete(e, out)
        elif isinstance(t, TBag) or isinstance(t, TList):
            assert out not in free_vars(e)
            x = self.fv(t.t, "x")
            return SSeq(
                self.initialize_native_list(out),
                SForEach(x, e, SCall(out, "add", [x])))
        elif isinstance(t, TSet):
            if isinstance(e, EUnaryOp) and e.op == UOp.Distinct:
                return self.construct_concrete(t, e.e, out)
            x = self.fv(t.t, "x")
            return SSeq(
                self.initialize_native_set(out),
                SForEach(x, e, SCall(out, "add", [x])))
        elif isinstance(t, TMap):
            return SSeq(
                self.initialize_native_map(out),
                self.construct_map(t, e, out))
        elif isinstance(t, THandle):
            return SEscape("{indent}{lhs} = {rhs};\n", ["lhs", "rhs"], [out, e])
        elif is_scalar(t):
            return SEscape("{indent}{lhs} = {rhs};\n", ["lhs", "rhs"], [out, e])
        else:
            h = extension_handler(type(t))
            if h is not None:
                return h.codegen(e, self.state_exps, out=out)
            raise NotImplementedError(t, e, out)

    def construct_map(self, t, e, out):
        if isinstance(e, ECond):
            return SIf(e.cond,
                construct_map(t, e.then_branch, out),
                construct_map(t, e.else_branch, out))
        elif isinstance(e, EMakeMap2):
            k = self.fv(t.k, "k")
            v = self.fv(t.v, "v")
            return SForEach(k, e.e,
                SMapUpdate(out, k, v,
                    self.construct_concrete(t.v, e.value.apply_to(k), v)))
        else:
            raise NotImplementedError(e)

    def initialize_native_list(self, e) -> Stm:
        return SNoOp() # C++ does default-initialization

    def initialize_native_set(self, e) -> Stm:
        return SNoOp() # C++ does default-initialization

    def initialize_native_map(self, e) -> Stm:
        return SNoOp() # C++ does default-initialization

    # def visit_EListGet(self, e, indent):
    #     assert type(e.e.type) is TList
    #     return self.visit(EEscape("{l}[{i}]", ["l", "i"], [e.e, e.index]).with_type(e.e.type.t))

    def visit_ENative(self, e):
        assert e.e == ENum(0)
        v = self.fv(e.type, "tmp")
        self.declare(v)
        return v.id

    def visit_EMakeRecord(self, e):
        t = self.visit(e.type, "")
        exps = [self.visit(ee) for (f, ee) in e.fields]
        return "({}({}))".format(t, ", ".join(exps))

    def visit_EHandle(self, e):
        assert e.addr == ENum(0), repr(e)
        return self.visit(ENull().with_type(e.type))

    def visit_EArrayGet(self, e):
        a = self.visit(e.a)
        i = self.visit(e.i)
        return "{}[{}]".format(a, i)

    def visit_EListGet(self, e):
        l = self.to_lvalue(e.e)
        i = self.fv(INT)
        return self.visit(ELet(e.index, ELambda(i,
            ECond(EAll([EGe(i, ZERO), ELt(i, EEscape("{l}.size()", ("l",), (l,)).with_type(INT))]),
                EEscape("{l}[{i}]", ("l", "i"), (l, i)).with_type(e.type),
                evaluation.construct_value(e.type)).with_type(e.type))).with_type(e.type))

    def visit_EArrayIndexOf(self, e):
        assert isinstance(e.a, EVar) # TODO: make this fast when this is false
        it = self.fv(TNative("{}::const_iterator".format(self.visit(e.a.type, "").strip())), "cursor")
        res = self.fv(INT, "index")
        self.visit(seq([
            SDecl(it.id, EEscape("std::find({a}.begin(), {a}.end(), {x})", ("a", "x"), (e.a, e.x)).with_type(it.type)),
            SDecl(res.id, ECond(
                EEq(it, EEscape("{a}.end()", ("a",), (e.a,)).with_type(it.type)),
                ENum(-1).with_type(INT),
                EEscape("({it} - {a}.begin())", ("it", "a",), (it, e.a,)).with_type(INT)).with_type(INT))]))
        return res.id

    def visit_SArrayAlloc(self, s):
        a = self.visit(s.a)
        cap = self.visit(s.capacity)
        self.write_stmt(a, " = std::move(", self.visit(s.a.type, ""), "(", cap, "));")

    def visit_SEnsureCapacity(self, s):
        a = self.visit(s.a)
        cap = self.visit(s.capacity)
        self.write_stmt(a, ".resize(", cap, ");")

    def visit_EMakeMap2(self, e):
        m = self.fv(e.type)
        self.declare(m)
        x = self.fv(e.type.k)
        self.visit(SForEach(x, e.e, SMapPut(m, x, e.value.apply_to(x))))
        return m.id

    def visit_EHasKey(self, e):
        map = self.visit(e.map)
        key = self.visit(e.key)
        return "{map}.find({key}) != {map}.end()".format(map=map, key=key)

    def visit_EMapGet(self, e):
        return self.native_map_get(
            e,
            lambda out: self.construct_concrete(
                e.map.type.v,
                evaluation.construct_value(e.map.type.v),
                out))

    def visit_SMapUpdate(self, update):
        map = self.visit(update.map)
        key = self.visit(update.key)
        self.begin_statement()
        self.write("{decl} = {map}[{key}];\n".format(
            decl=self.visit(TRef(update.val_var.type), update.val_var.id),
            map=map,
            key=key))
        self.end_statement()
        self.visit(update.change)

    def visit_SMapPut(self, update):
        map = self.visit(update.map)
        key = self.visit(update.key)
        val = self.fv(update.value.type)
        self.declare(val, update.value)
        val = self.visit(EMove(val))
        self.begin_statement()
        self.write(map, ".emplace(", key, ", ", val, ");")
        self.end_statement()

    def visit_SMapDel(self, update):
        map = self.visit(update.map)
        key = self.visit(update.key)
        self.begin_statement()
        self.write(map, ".erase(", key, ");")
        self.end_statement()

    def visit_Exp(self, e):
        h = extension_handler(type(e))
        if h is not None:
            v = self.fv(e.type)
            self.declare(v)
            self.visit(h.codegen(e, self.state_exps, out=v))
            return v.id
        else:
            raise NotImplementedError(e)

    def visit_EVar(self, e):
        return e.id

    def visit_EEnumEntry(self, e):
        return e.name

    def visit_ENum(self, e):
        if isinstance(e.type, TFloat):
            return "{!r}f".format(float(e.val))
        return repr(e.val)

    def visit_EStr(self, e):
        return json.dumps(e.val)

    def visit_EEnumToInt(self, e):
        return "static_cast<int>(" + self.visit(e.e) + ")"

    def visit_EBoolToInt(self, e):
        return "static_cast<int>(" + self.visit(e.e) + ")"

    # def _is_concrete(self, e):
    #     if is_scalar(e.type):
    #         return True
    #     elif type(e.type) in [TMap, TSet, TBag]:
    #         return False
    #     return True

    def histogram(self, e) -> EVar:
        t = TMap(e.type.t, INT)
        hist = self.fv(t, "hist")
        x = self.fv(e.type.t)
        val = self.fv(INT, "val")
        self.declare(hist)
        self.visit(self.initialize_native_map(hist))
        self.visit(SForEach(x, e,
            SMapUpdate(hist, x, val,
                SAssign(val, EBinOp(val, "+", ONE).with_type(INT)))))
        return hist

    def _eq(self, e1, e2):
        return self.visit(EEscape("({e1} == {e2})", ["e1", "e2"], [e1, e2]).with_type(BOOL))

    def visit_EBinOp(self, e):
        op = e.op
        if op == "+" and (isinstance(e.e1.type, TBag) or isinstance(e.e1.type, TSet)):
            raise NotImplementedError("adding collections: {}".format(e))
        elif op == "==":
            return self._eq(e.e1, e.e2)
        elif op == "===":
            # rewrite deep-equality test into regular equality
            op = "=="
        elif op == "!=":
            return self.visit(ENot(EEq(e.e1, e.e2)))
        elif op == BOp.Or:
            return self.visit(ECond(e.e1, T, e.e2).with_type(BOOL))
        elif op == BOp.And:
            return self.visit(ECond(e.e1, e.e2, F).with_type(BOOL))
        elif op == "-" and is_collection(e.type):
            t = e.type
            v = self.fv(t, "v")
            x = self.fv(t.t, "x")
            self.declare(v, e.e1)
            self.visit(SForEach(x, e.e2, SCall(v, "remove", [x])))
            return v.id
        elif op == BOp.In:
            if isinstance(e.e2.type, TSet):
                return self.test_set_containment_native(e.e2, e.e1)
            else:
                t = BOOL
                res = self.fv(t, "found")
                x = self.fv(e.e1.type, "x")
                label = fresh_name("label")
                self.visit(seq([
                    SDecl(res.id, F),
                    SEscapableBlock(label,
                        SForEach(x, e.e2, SIf(
                            EBinOp(x, "==", e.e1).with_type(BOOL),
                            seq([SAssign(res, T), SEscapeBlock(label)]),
                            SNoOp())))]))
                return res.id
        return "({e1} {op} {e2})".format(e1=self.visit(e.e1), op=op, e2=self.visit(e.e2))

    def test_set_containment_native(self, set : Exp, elem : Exp) -> str:
        return self.visit(EEscape("{set}.find({elem}) != {set}.end()", ["set", "elem"], [set, elem]).with_type(BOOL))

    def visit_SScoped(self, s):
        self.begin_statement()
        with self.block():
            self.visit(s.s)
        self.end_statement()

    def for_each(self, iterable : Exp, body) -> str:
        """Body is function: exp -> stm"""
        if isinstance(iterable, EEmptyList):
            return ""
        elif isinstance(iterable, ESingleton):
            return self.visit(SScoped(body(iterable.e)))
        elif isinstance(iterable, ECond):
            v = self.fv(iterable.type.t, "v")
            new_body = body(v)
            assert isinstance(new_body, Stm)
            return self.visit(SIf(iterable.cond,
                SForEach(v, iterable.then_branch, new_body),
                SForEach(v, iterable.else_branch, new_body)))
        elif isinstance(iterable, EMap):
            return self.for_each(
                iterable.e,
                lambda v: body(iterable.f.apply_to(v)))
        elif isinstance(iterable, EUnaryOp) and iterable.op == UOp.Distinct:
            tmp = self.fv(TSet(iterable.type.t), "tmp")
            self.declare(tmp)
            self.visit(self.initialize_native_set(tmp))
            self.for_each(iterable.e, lambda x: SIf(
                ENot(EBinOp(x, BOp.In, tmp).with_type(BOOL)),
                seq([body(x), SCall(tmp, "add", [x])]),
                SNoOp()))
        elif isinstance(iterable, EFilter):
            return self.for_each(iterable.e, lambda x: SIf(iterable.p.apply_to(x), body(x), SNoOp()))
        elif isinstance(iterable, EBinOp) and iterable.op == "+":
            self.for_each(iterable.e1, body)
            self.for_each(iterable.e2, body)
        elif isinstance(iterable, EBinOp) and iterable.op == "-":
            t = TList(iterable.type.t)
            e = self.visit(EBinOp(iterable.e1, "-", iterable.e2).with_type(t))
            return self.for_each(EEscape(e, (), ()).with_type(t), body)
        elif isinstance(iterable, EFlatMap):
            v = self.fv(iterable.type.t)
            new_body = body(v)
            assert isinstance(new_body, Stm)
            return self.for_each(iterable.e,
                body=lambda bag: SForEach(v, iterable.f.apply_to(bag), new_body))
        elif isinstance(iterable, EListSlice):
            s = self.fv(INT, "start")
            e = self.fv(INT, "end")
            l = self.visit(iterable.e)
            self.declare(s, iterable.start)
            self.declare(e, iterable.end)
            return self.visit(SWhile(ELt(s, e), SSeq(
                body(EEscape("{l}[{i}]", ("l", "i"), (iterable.e, s)).with_type(iterable.type.t)),
                SAssign(s, EBinOp(s, "+", ONE).with_type(INT)))))
        elif isinstance(iterable, ECall) and iterable.func in self.queries:
            q = self.queries[iterable.func]
            return self.for_each(subst(q.ret, { a : v for ((a, t), v) in zip(q.args, iterable.args) }), body)
        elif isinstance(iterable, ELet):
            return self.for_each(iterable.f.apply_to(iterable.e), body)
        else:
            assert is_collection(iterable.type)
            x = self.fv(iterable.type.t, "x")
            return self.for_each_native(x, iterable, body(x))

    def for_each_native(self, x : EVar, iterable, body):
        if isinstance(iterable, EMapKeys):
            map = self.visit(iterable.e)
            pair = self.fv(TNative("const auto &"))
            self.begin_statement()
            self.write("for (", self.visit(pair.type, pair.id), " : ", map, ") ")
            with self.block():
                self.visit(SSeq(
                    SDecl(x.id, EEscape("{p}.first", ("p",), (pair,)).with_type(x.type)),
                    body))
            self.end_statement()
            return
        iterable = self.visit(iterable)
        self.begin_statement()
        self.write("for (", self.visit(x.type, x.id), " : ", iterable, ") ")
        with self.block():
            self.visit(body)
        self.end_statement()

    def visit_SForEach(self, for_each):
        id = for_each.id
        iter = for_each.iter
        body = for_each.body
        self.for_each(iter, lambda x: SSeq(SDecl(id.id, x), body))

    def find_one(self, iterable):
        v = self.fv(iterable.type.t, "v")
        label = fresh_name("label")
        x = self.fv(iterable.type.t, "x")
        decl = SDecl(v.id, evaluation.construct_value(v.type))
        find = SEscapableBlock(label,
            SForEach(x, iterable, seq([
                SAssign(v, x),
                SEscapeBlock(label)])))
        self.visit(seq([decl, find]))
        return v.id

    def min_or_max(self, op, e, f):
        if isinstance(e, EBinOp) and e.op == "+" and isinstance(e.e1, ESingleton) and isinstance(e.e2, ESingleton):
            # argmin_f ([a] + [b]) ---> f(a) < f(b) ? a : b
            return self.visit(ECond(
                EBinOp(f.apply_to(e.e1.e), op, f.apply_to(e.e2.e)).with_type(BOOL),
                e.e1.e,
                e.e2.e).with_type(e.e1.e.type))
        out = self.fv(e.type.t, "min" if op == "<" else "max")
        first = self.fv(BOOL, "first")
        x = self.fv(e.type.t, "x")
        decl1 = SDecl(out.id, evaluation.construct_value(out.type))
        decl2 = SDecl(first.id, T)
        find = SForEach(x, e,
            SIf(EBinOp(
                    first,
                    BOp.Or,
                    EBinOp(f.apply_to(x), op, f.apply_to(out)).with_type(BOOL)).with_type(BOOL),
                seq([SAssign(first, F), SAssign(out, x)]),
                SNoOp()))
        self.visit(seq([decl1, decl2, find]))
        return out.id

    def visit_EArgMin(self, e):
        return self.min_or_max("<", e.e, e.f)

    def visit_EArgMax(self, e):
        return self.min_or_max(">", e.e, e.f)

    def visit_EMap(self, e):
        return self.visit(self.to_lvalue(e))

    def visit_EFilter(self, e):
        return self.visit(self.to_lvalue(e))

    def reverse_inplace(self, e : EVar) -> Stm:
        assert isinstance(e.type, TList)
        return SEscape("{indent}std::reverse({e}.begin(), {e}.end());\n", ("e",), (e,))

    def visit_EUnaryOp(self, e):
        op = e.op
        if op == UOp.The:
            return self.find_one(e.e)
        elif op == UOp.Sum:
            type = e.e.type.t
            res = self.fv(type, "sum")
            x = self.fv(type, "x")
            self.visit(seq([
                SDecl(res.id, ENum(0).with_type(type)),
                SForEach(x, e.e, SAssign(res, EBinOp(res, "+", x).with_type(type)))]))
            return res.id
        elif op == UOp.Length:
            arg = EVar("x").with_type(e.e.type.t)
            return self.visit(EUnaryOp(UOp.Sum, EMap(e.e, ELambda(arg, ONE)).with_type(INT_BAG)).with_type(INT))
        elif op == UOp.All:
            arg = EVar("x").with_type(e.e.type.t)
            return self.visit(EUnaryOp(UOp.Empty, EFilter(e.e, ELambda(arg, ENot(arg))).with_type(INT_BAG)).with_type(INT))
        elif op == UOp.Any:
            arg = EVar("x").with_type(e.e.type.t)
            return self.visit(EUnaryOp(UOp.Exists, EFilter(e.e, ELambda(arg, arg)).with_type(INT_BAG)).with_type(INT))
        elif op == UOp.Empty:
            iterable = e.e
            v = self.fv(BOOL, "v")
            label = fresh_name("label")
            x = self.fv(iterable.type.t, "x")
            decl = SDecl(v.id, T)
            find = SEscapableBlock(label,
                SForEach(x, iterable, seq([
                    SAssign(v, F),
                    SEscapeBlock(label)])))
            self.visit(seq([decl, find]))
            return v.id
        elif op == UOp.Exists:
            return self.visit(ENot(EUnaryOp(UOp.Empty, e.e).with_type(BOOL)))
        elif op in ("-", UOp.Not):
            ee = self.visit(e.e)
            op_str = "!" if op == UOp.Not else op
            return "({op}({ee}))".format(op=op_str, ee=ee)
        elif op == UOp.Distinct:
            v = self.fv(e.type, "v")
            self.declare(v, e)
            return v.id
        elif op == UOp.AreUnique:
            s = self.fv(TSet(e.e.type.t), "unique_elems")
            u = self.fv(BOOL, "is_unique")
            x = self.fv(e.e.type.t)
            label = fresh_name("label")
            self.visit(seq([
                SDecl(s.id, EEmptyList().with_type(s.type)),
                SDecl(u.id, T),
                SEscapableBlock(label,
                    SForEach(x, e.e,
                        SIf(EEscape("{s}.find({x}) != {s}.end()", ("s", "x"), (s, x)).with_type(BOOL),
                            seq([SAssign(u, F), SEscapeBlock(label)]),
                            SEscape("{indent}{s}.insert({x});\n", ("s", "x"), (s, x)))))]))
            return u.id
        elif op == UOp.Reversed:
            v = self.fv(e.type, "v")
            self.declare(v, e.e)
            self.visit(self.reverse_inplace(v))
            return v.id
        else:
            raise NotImplementedError(op)

    def visit_EGetField(self, e):
        ee = self.visit(e.e)
        op = "."
        if isinstance(e.e.type, THandle):
            # Ugh, we really need Cozy to know about partial functions...
            # Cozy doesn't know that handle types (aka pointers) can be null.
            # It assumes that reads of null pointers produce default-
            # constructed values, so we need to generate appropriate code.
            ee = EEscape(ee, (), ()).with_type(e.e.type)
            null = ENull().with_type(e.e.type)
            return self.visit(ECond(EEq(ee, null),
                EEscape("{ee}->val", ("ee",), (ee,)).with_type(e.type),
                evaluation.construct_value(e.type)).with_type(e.type))
        return "({ee}.{f})".format(ee=ee, f=e.f)

    def visit_ETuple(self, e):
        name = self.typename(e.type)
        args = [self.visit(arg) for arg in e.es]
        return "({}({}))".format(name, ", ".join(args))

    def visit_ETupleGet(self, e):
        if isinstance(e.e, ETuple):
            return self.visit(e.e.es[e.n])
        return self.visit_EGetField(EGetField(e.e, "_{}".format(e.n)))

    def visit_ECall(self, e):
        args = [self.visit(a) for a in e.args]
        if e.func in self.funcs:
            f = self.funcs[e.func]
            return "({})".format(f.body_string.format(**{ arg: "({})".format(val) for (arg, _), val in zip(f.args, args) }))
        elif e.func in self.queries:
            q = self.queries[e.func]
            body = subst(q.ret, { q.args[i][0] : EEscape(args[i], (), ()).with_type(q.args[i][1]) for i in range(len(q.args)) })
            return self.visit(body)
        else:
            raise Exception("unknown function {}".format(repr(e.func)))

    # def visit_ELet(self, e):
    #     v = self.fv(e.e.type, "v")
    #     setup1 = self.visit(SDecl(v.id, e.e), indent=indent)
    #     setup2, res = self.visit(e.f.apply_to(v), indent=indent)
    #     return (setup1 + setup2, res)

    def visit_object(self, e):
        raise NotImplementedError(e)

    def visit_SEscape(self, s):
        indent = self.get_indent()
        body = s.body_string
        args = s.args
        if not args:
            self.write(body.format(indent=indent))
        else:
            args = [self.visit(arg) for arg in args]
            self.write(body.format(indent=indent, **dict(zip(s.arg_names, args))))

    def visit_EEscape(self, e):
        body = e.body_string
        args = e.args
        if not args:
            return body
        args = [self.visit(arg) for arg in args]
        return "(" + body.format(**dict(zip(e.arg_names, args))) + ")"

    def visit_SNoOp(self, s):
        pass

    # def copy_to(self, lhs, rhs):
    #     if isinstance(lhs.type, TBag):
    #         cl, el = self.visit(lhs, indent)
    #         x = self.fv(lhs.type.t, "x")
    #         # TODO: hacky use of EVar ahead! We need an EEscape, like SEscape
    #         return cl + self.visit(SForEach(x, rhs, SCall(EVar(el).with_type(lhs.type), "add", [x])), indent=indent)
    #     else:
    #         return self.visit(SAssign(lhs, rhs), indent)

    def visit_EMove(self, e):
        return "std::move(" + self.visit(e.e) + ")"

    def declare(self, v : EVar, initial_value : Exp = None):
        if initial_value is not None and is_scalar(v.type):
            iv = self.visit(initial_value)
            self.write_stmt(self.visit(v.type, v.id), " = ", iv, ";")
        else:
            self.write_stmt(self.visit(v.type, v.id), ";")
            if initial_value is not None:
                self.visit(self.construct_concrete(v.type, initial_value, v))

    def visit_SAssign(self, s):
        if is_scalar(s.rhs.type):
            self.write_stmt(self.visit(s.lhs), " = ", self.visit(s.rhs), ";")
        else:
            v = self.fv(s.lhs.type)
            self.declare(v, s.rhs)
            self.write_stmt(self.visit(s.lhs), " = ", self.visit(EMove(v).with_type(v.type)), ";")

    def visit_SDecl(self, s):
        assert isinstance(s.id, str)
        t = s.val.type
        return self.declare(EVar(s.id).with_type(t), s.val)

    def visit_SSeq(self, s):
        for ss in break_seq(s):
            self.visit(ss)

    def visit_SIf(self, s):
        cond = self.visit(s.cond)
        self.begin_statement()
        self.write("if (", cond, ") ")
        with self.block():
            self.visit(s.then_branch)
        if not isinstance(s.else_branch, SNoOp):
            self.write(" else ")
            with self.block():
                self.visit(s.else_branch)
        self.end_statement()

    def visit_ECond(self, e):
        if e.cond == T:
            return self.visit(e.then_branch)
        elif e.cond == F:
            return self.visit(e.else_branch)
        v = self.fv(e.type, "v")
        self.declare(v)
        self.visit(SIf(e.cond, SAssign(v, e.then_branch), SAssign(v, e.else_branch)))
        return v.id

    def visit_SCall(self, call):
        h = extension_handler(type(call.target.type))
        if h is not None:
            return self.visit(h.implement_stmt(call, self.state_exps))

        target = self.visit(call.target)
        args = [self.visit(a) for a in call.args]
        self.begin_statement()

        if type(call.target.type) in (TBag, TList):
            if call.func == "add":
                self.write(target, ".push_back(", args[0], ");")
            elif call.func == "remove":
                v = self.fv(TNative("auto"), "it")
                self.write("auto ", v.id, "(::std::find(", target, ".begin(), ", target, ".end(), ", args[0], "));")
                self.end_statement()
                self.begin_statement()
                self.write("if (", v.id, " != ", target, ".end()) { ", target, ".erase(", v.id, "); }")
            else:
                raise NotImplementedError(call.func)
        elif isinstance(call.target.type, TSet):
            if call.func == "add":
                self.write(target, ".insert(", args[0], ");")
            elif call.func == "remove":
                self.write(target, ".erase(", target, ".find(", args[0], "));")
            else:
                raise NotImplementedError(call.func)
        else:
            raise NotImplementedError()

        self.end_statement()

    def nbits(self, t):
        if t == BOOL:
            return 1
        elif isinstance(t, TEnum):
            return common.integer_log2_round_up(len(t.cases))
        else:
            return None

    def declare_field(self, name, type):
        self.begin_statement()
        nbits = self.nbits(type)
        self.write(
            self.visit(type, name),
            " : {}".format(nbits) if nbits else "",
            ";")
        self.end_statement()

    def define_type(self, toplevel_name, t, name, sharing):
        if isinstance(t, TEnum):
            self.begin_statement()
            self.write("enum ", name, " ")
            with self.block():
                for case in t.cases:
                    self.begin_statement()
                    self.write(case, ",")
                    self.end_statement()
            self.write(";")
            self.end_statement()
        elif isinstance(t, THandle):
            fields = [("val", t.value_type)]
            self.begin_statement()
            self.write("struct ", name, " ")
            with self.block():
                with self.deindented(): self.write_stmt("public:")
                for (f, ft) in fields:
                    self.declare_field(f, ft)
                with self.deindented(): self.write_stmt("private:")
            self.write(";")
            self.end_statement()

            # s = "struct {name} {{\n".format(indent=indent, name=name)
            # s += "public:\n".format(indent=indent)
            # for (f, ft) in fields:
            #     s += self.declare_field(f, ft)
            # s += "private:\n".format(indent=indent)
            # s += "friend class {toplevel_name};\n".format(indent=indent+INDENT, toplevel_name=toplevel_name)
            # for group in sharing.get(t, []):
            #     s += "union {{\n".format(indent=indent+INDENT)
            #     for gt in group:
            #         intrusive_data = gt.intrusive_data(t)
            #         s += "struct {{\n".format(indent=indent+INDENT*2)
            #         for (f, ft) in intrusive_data:
            #             s += "{field_decl};\n".format(indent=indent+INDENT*3, field_decl=self.visit(ft, f))
            #         s += "}};\n".format(indent=indent+INDENT*2)
            #     s += "}};\n".format(indent=indent+INDENT)
            # s += "}};\n".format(indent=indent)
            # return s
        elif isinstance(t, TRecord):
            self.begin_statement()
            self.write("struct ", name, " ")
            with self.block():
                for f, ft in t.fields:
                    self.declare_field(f, ft)

                self.write_stmt("inline ", name, "() { }")
                self.begin_statement()
                self.write("inline ", name, "(")
                self.visit_args([("_" + f, t) for (f, t) in t.fields])
                self.write(") : ")
                for i, (f, ft) in enumerate(t.fields):
                    if i > 0:
                        self.write(", ")
                    self.write(f, "(::std::move(_", f, "))")
                self.write(" { }")
                self.end_statement()

                self.begin_statement()
                self.write("inline bool operator==(const ", name, "& other) const ")
                with self.block():
                    this = EEscape("(*this)", (), ()).with_type(t)
                    other = EVar("other").with_type(t)
                    r = self.visit(EAll([
                        EEq(EGetField(this, f).with_type(ft), EGetField(other, f).with_type(ft))
                        for f, ft in t.fields]))
                    self.begin_statement()
                    self.write("return ", r, ";")
                    self.end_statement()
                self.end_statement()
            self.write(";")
            self.end_statement()
        elif isinstance(t, TTuple):
            return self.define_type(toplevel_name, TRecord(tuple(("_{}".format(i), t.ts[i]) for i in range(len(t.ts)))), name, sharing);
        else:
            return ""

    def setup_types(self, spec, state_exps, sharing):
        self.types.clear()
        names = { t : name for (name, t) in spec.types }
        for t in itertools.chain(all_types(spec), *[all_types(e) for v, e in state_exps.items()]):
            if t not in self.types and type(t) in [THandle, TRecord, TTuple, TEnum]:
                name = names.get(t, self.fn("Type"))
                self.types[t] = name

    def visit_args(self, args):
        for (i, (v, t)) in enumerate(args):
            assert isinstance(v, str)
            assert isinstance(t, Type)
            if i > 0:
                self.write(", ")
            self.write(self.visit(t, v))

    def _hasher(self, t : Type) -> str:
        if isinstance(t, THandle):
            return "std::hash<{}>".format(self.visit(t, ""))
        try:
            n = self.typename(t)
            return "_Hash{}".format(n)
        except KeyError:
            return "std::hash<{}>".format(self.visit(t, ""))

    def compute_hash_1(self, e : Exp) -> Exp:
        return EEscape("{hasher}()({{e}})".format(hasher=self._hasher(e.type)), ("e",), (e,)).with_type(TNative("std::size_t"))

    def compute_hash(self, fields : [Exp]) -> Stm:
        hc = self.fv(TNative("std::size_t"), "hash_code")
        s = SDecl(hc.id, ENum(0).with_type(hc.type))
        for f in fields:
                    # return SAssign(out, )
            s = SSeq(s, SAssign(hc,
                EEscape("({hc} * 31) ^ ({h})", ("hc", "h"),
                    (hc, self.compute_hash_1(f))).with_type(TNative("std::size_t"))))
        s = SSeq(s, SEscape("{indent}return {e};\n", ("e",), (hc,)))
        return s

    @typechecked
    def visit_Spec(self, spec : Spec, state_exps : { str : Exp }, sharing, abstract_state=()):
        self.state_exps = state_exps
        self.funcs = { f.name: f for f in spec.extern_funcs }
        self.queries = { q.name: q for q in spec.methods if isinstance(q, Query) }
        self.vars = set(e.id for e in all_exps(spec) if isinstance(e, EVar))

        self.write("#pragma once\n")
        self.write("#include <algorithm>\n")
        self.write("#include <functional>\n")
        self.write("#include <vector>\n")
        self.write("#include <unordered_set>\n")
        self.write("#include <string>\n")
        if self.use_qhash:
            self.write("#include <QHash>\n")
        else:
            self.write("#include <unordered_map>\n")

        if spec.header:
            self.write("\n" + spec.header.strip() + "\n")

        self.write("{}\nclass {} {{\n".format(
            ("\n" + spec.docstring) if spec.docstring else "",
            spec.name))

        self.write("public:\n")

        print("Setting up auxiliary types...")
        self.setup_types(spec, state_exps, sharing)
        with self.indented():
            for t, name in self.types.items():
                self.define_type(spec.name, t, name, sharing)
                self.begin_statement()
                if isinstance(t, THandle):
                    # No overridden hash code! We use pointers instead.
                    continue
                self.write("struct _Hash", name, " ")
                with self.block():
                    self.write_stmt("typedef ", spec.name, "::", name, " argument_type;")
                    self.write_stmt("typedef std::size_t result_type;")
                    self.begin_statement()
                    self.write("result_type operator()(const argument_type& x) const noexcept ")
                    x = EVar("x").with_type(t)
                    if isinstance(t, TEnum):
                        fields = [EEnumToInt(x).with_type(INT)]
                    elif isinstance(t, TRecord):
                        fields = [EGetField(x, f).with_type(ft) for (f, ft) in t.fields]
                    elif isinstance(t, TTuple):
                        fields = [ETupleGet(x, n).with_type(tt) for (n, tt) in enumerate(t.ts)]
                    else:
                        raise NotImplementedError(t)
                    with self.block():
                        self.visit(self.compute_hash(fields))
                    self.end_statement()
                self.write(";")
                self.end_statement()

        print("Setting up member variables...")
        self.write("protected:\n")
        with self.indented():
            for name, t in spec.statevars:
                self.statevar_name = name
                self.declare_field(name, t)

        self.write("public:\n")
        with self.indented():
            print("Generating constructors...")

            # default constructor
            self.begin_statement()
            self.write("inline ", spec.name, "() ")
            with self.block():
                for name, t in spec.statevars:
                    initial_value = state_exps[name]
                    fvs = free_vars(initial_value)
                    initial_value = subst(initial_value, {v.id : evaluation.construct_value(v.type) for v in fvs})
                    self.visit(self.construct_concrete(t, initial_value, EVar(name).with_type(t)))
            self.end_statement()

            # explicit constructor
            if abstract_state:
                self.begin_statement()
                self.write("explicit inline ", spec.name, "(")
                self.visit_args(abstract_state)
                self.write(") ")
                with self.block():
                    for name, t in spec.statevars:
                        initial_value = state_exps[name]
                        self.visit(self.construct_concrete(t, initial_value, EVar(name).with_type(t)))
                self.end_statement()

            # disable copy constructor (TODO: support this in the future?)
            self.begin_statement()
            self.write(spec.name, "(const ", spec.name, "& other) = delete;")
            self.end_statement()

            # generate methods
            for op in spec.methods:
                print("Generating method {}...".format(op.name))
                self.visit(op)
        self.write("};\n")

        if spec.footer:
            self.write("\n", spec.footer)
            if not spec.footer.endswith("\n"):
                self.write("\n")
