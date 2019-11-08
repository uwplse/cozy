from collections import OrderedDict
import json
import itertools

from cozy import common, evaluation
from cozy.common import fresh_name, extend, typechecked
from cozy.syntax import (
    Spec, Query,
    Visibility, UOp, BOp,
    Type, INT, BOOL, TNative, TSet, TList, TBag, THandle, TEnum, TTuple, TRecord, TFloat,
    Exp, EVar, ENum, EFALSE, ETRUE, ZERO, ENull, EEq, ELt, ENot, ECond, EAll,
    EEnumEntry, ETuple, ETupleGet, EGetField,
    Stm, SNoOp, SIf, SDecl, SSeq, seq, SForEach, SAssign, SCall)
from cozy.target_syntax import TArray, TRef, EEnumToInt, EMapKeys, SReturn
from cozy.syntax_tools import pprint, all_types, fresh_var, subst, free_vars, all_exps, break_seq, shallow_copy
from cozy.typecheck import is_collection, is_scalar

from .misc import CodeGenerator, indent_lines, EEscape, SEscape, EMove, SScoped
from .optimization import simplify_and_optimize

class CxxPrinter(CodeGenerator):

    def __init__(self, out, use_qhash : bool = False):
        super().__init__(out=out)
        self.types = OrderedDict()
        self.funcs = {}
        self.queries = {}
        self.labels = {}
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

    def visit_TNative(self, t, name):
        return "{} {}".format(t.name, name)

    def visit_TTreeMultisetNative(self, t, name):
        return "std::multiset< {} > {}".format(self.visit(t.elem_type, ""), name)

    def visit_TInt(self, t, name):
        return "int {}".format(name)

    def visit_TLong(self, t, name):
        return "long {}".format(name)

    def visit_TFloat(self, t, name):
        return "float {}".format(name)

    def visit_TBool(self, t, name):
        return "bool {}".format(name)

    def visit_TRef(self, t, name):
        return self.visit(t.elem_type, "&{}".format(name))

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
        return self.visit_TNativeMap(t, name)

    def visit_TList(self, t, name):
        return self.visit_TNativeList(t, name)

    def visit_TBag(self, t, name):
        return self.visit_TNativeList(t, name)

    def visit_TSet(self, t, name):
        return self.visit_TNativeSet(t, name)

    def visit_TNativeList(self, t, name):
        return "std::vector< {} > {}".format(self.visit(t.elem_type, ""), name)

    def visit_TNativeSet(self, t, name):
        return "std::unordered_set< {}, {} > {}".format(self.visit(t.elem_type, ""), self._hasher(t.elem_type), name)

    def visit_TArray(self, t, name):
        return "std::vector< {} > {}".format(self.visit(t.elem_type, ""), name)

    def visit_Type(self, t, name):
        raise NotImplementedError(t)

    def visit_TRecord(self, t, name):
        return "{} {}".format(self.typename(t), name)

    def visit_TTuple(self, t, name):
        return "{} {}".format(self.typename(t), name)

    def visit_TEnum(self, enum, name):
        return "{} {}".format(self.typename(enum), name)

    def visit_TVector(self, t, name):
        return "{}[{}]".format(self.visit(t.elem_type, name), t.index)

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
        l = fresh_name("label")
        with extend(self.labels, s.label, l):
            self.visit(SScoped(s.body))
            self.write(l, ":\n")

    def visit_SEscapeBlock(self, s):
        self.begin_statement()
        self.write("goto ", self.labels[s.label], ";")
        self.end_statement()

    def visit_Query(self, q):
        if q.visibility != Visibility.Public:
            return ""
        ret_exp = q.ret
        ret_type = ret_exp.type
        if is_collection(ret_type):
            x = self.fv(ret_type.elem_type, "x")
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
                self.visit(simplify_and_optimize(SForEach(x, ret_exp, SEscape("{indent}_callback({x});\n", ["x"], [x]))))
            self.end_statement()
        else:
            if q.docstring:
                self.write(indent_lines(q.docstring, self.get_indent()), "\n")
            self.begin_statement()
            self.write("inline ", self.visit(ret_type, ""), " ", q.name, "(")
            self.visit_args(q.args)
            self.write(") ")
            with self.block():
                self.visit(simplify_and_optimize(SReturn(ret_exp)))
            self.end_statement()

    def visit_Op(self, q):
        if q.docstring:
            self.write(indent_lines(q.docstring, self.get_indent()), "\n")
        self.begin_statement()
        self.write("inline void ", q.name, " (")
        self.visit_args(q.args)
        self.write(") ")
        with self.block():
            self.visit(simplify_and_optimize(q.body))
        self.end_statement()

    def visit_ENull(self, e):
        return "nullptr"

    def visit_EBool(self, e):
        return "true" if e.val else "false"

    def visit_EEmptyList(self, e):
        t = self.visit(e.type, "")
        return "(" + t + "())"

    def visit_EEmptyMap(self, e):
        t = self.visit(e.type, "")
        return "(" + t + "())"

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

    def visit_EArrayLen(self, e):
        a = self.visit(e.e)
        return "{}.size()".format(a)

    def visit_EListGet(self, e):
        l = self.visit(e.e)
        i = self.visit(e.index)
        return self.visit(EEscape(
            "(" + i + " >= 0 && " + i + " < " + l + ".size()) ? " + l + "[" + i + "] : {default}",
            ("default",),
            (evaluation.construct_value(e.type),)).with_type(e.type))

    def visit_EArrayIndexOf(self, e):
        if isinstance(e.a, EVar): pass
        elif isinstance(e.a, ETupleGet) and isinstance(e.a.e, EVar): pass
        else: raise NotImplementedError("finding index of non-var array") # TODO: make this fast when this is false
        it = self.fv(TNative("{}::const_iterator".format(self.visit(e.a.type, "").strip())), "cursor")
        res = self.fv(INT, "index")
        self.visit(seq([
            SDecl(it, EEscape("std::find({a}.begin(), {a}.end(), {x})", ("a", "x"), (e.a, e.x)).with_type(it.type)),
            SDecl(res, ECond(
                EEq(it, EEscape("{a}.end()", ("a",), (e.a,)).with_type(it.type)),
                ENum(-1).with_type(INT),
                EEscape("({it} - {a}.begin())", ("it", "a",), (it, e.a,)).with_type(INT)).with_type(INT))]))
        return res.id

    def visit_SArrayAlloc(self, s):
        a = self.visit(s.a.type, s.a.id)
        cap = self.visit(s.capacity)
        self.write_stmt(a, " = std::move(", self.visit(s.a.type, ""), "(", cap, "));")

    def visit_SEnsureCapacity(self, s):
        a = self.visit(s.a)
        cap = self.visit(s.capacity)
        self.write_stmt(a, ".resize(", cap, ");")

    def visit_EMakeMap2(self, e):
        m = self.fv(e.type)
        self.declare(m, e)
        return m.id

    def visit_EMapKeys(self, e):
        key = self.fv(e.type.elem_type)
        keys = self.fv(e.type)
        self.declare(keys)
        add_to_keys = SCall(keys, "add", [key])
        self.visit(SForEach(key, e, add_to_keys))
        return keys.id

    def visit_EHasKey(self, e):
        map = self.visit(e.map)
        key = self.visit(e.key)
        return "{map}.find({key}) != {map}.end()".format(map=map, key=key)

    def visit_EMapGet(self, e):
        emap = self.visit(e.map)
        if self.use_qhash:
            ekey = self.visit(e.key)
            return "{}.value({})".format(emap, ekey)
        t = self.visit(e.map.type, "").strip() + "::const_iterator"
        iterator = self.fv(TNative(t), "map_iterator")
        self.declare(iterator, EEscape(emap + ".find({key})", ("key",), (e.key,)))
        return self.visit(ECond(
            EEscape("{it} == " + emap + ".end()", ("it",), (iterator,)).with_type(BOOL),
            evaluation.construct_value(e.type),
            EEscape("{it}->second", ("it",), (iterator,)).with_type(e.type)).with_type(e.type))

    def visit_SMapUpdate(self, update):
        map = self.visit(update.map)
        key = self.visit(update.key)
        t = self.visit(update.map.type, "").strip() + "::iterator"
        iterator = self.fv(TNative(t), "map_iterator")
        self.declare(iterator, EEscape(map + ".find(" + key + ")", (), ()))
        self.visit(SIf(
            EEscape("{it} == " + map + ".end()", ("it",), (iterator,)).with_type(BOOL),
            SAssign(iterator, EEscape(map + ".emplace(" + key + ", {value}).first", ("value",), (evaluation.construct_value(update.val_var.type),)).with_type(iterator.type)),
            SNoOp()))
        self.begin_statement()
        self.write("{decl} = {it}->second;\n".format(
            decl=self.visit(TRef(update.val_var.type), update.val_var.id),
            it=iterator.id))
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

    def visit_ESorted(self, e):
        # TODO(zhen): implement this
        raise NotImplementedError("{} is not implemented. Try a larger timeout for its improved version".format(e))

    def visit_Exp(self, e):
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

    def _eq(self, e1, e2):
        return self.visit(EEscape("({e1} == {e2})", ["e1", "e2"], [e1, e2]).with_type(BOOL))

    def visit_EBinOp(self, e):
        op = e.op
        if op == "==":
            return self._eq(e.e1, e.e2)
        elif op == "===":
            # rewrite deep-equality test into regular equality
            op = "=="
        elif op == "!=":
            return self.visit(ENot(EEq(e.e1, e.e2)))
        elif op == BOp.Or:
            return self.visit(ECond(e.e1, ETRUE, e.e2).with_type(BOOL))
        elif op == BOp.And:
            return self.visit(ECond(e.e1, e.e2, EFALSE).with_type(BOOL))
        elif op == BOp.In:
            if isinstance(e.e2.type, TSet):
                return self.test_set_containment_native(e.e2, e.e1)
            else:
                raise Exception("{!r} operator is supposed to be handled by simplify_and_optimize".format(op))
        return "({e1} {op} {e2})".format(e1=self.visit(e.e1), op=op, e2=self.visit(e.e2))

    def test_set_containment_native(self, set : Exp, elem : Exp) -> str:
        return self.visit(EEscape("{set}.find({elem}) != {set}.end()", ["set", "elem"], [set, elem]).with_type(BOOL))

    def visit_SScoped(self, s):
        self.begin_statement()
        with self.block():
            self.visit(s.s)
        self.end_statement()

    def visit_SForEach(self, for_each):
        loop_var = for_each.loop_var
        iterable = for_each.iter
        body = for_each.body
        if isinstance(iterable, EMapKeys):
            map = self.visit(iterable.e)
            pair = self.fv(TNative("const auto &"))
            self.begin_statement()
            self.write("for (", self.visit(pair.type, pair.id), " : ", map, ") ")
            with self.block():
                self.visit(SSeq(
                    SDecl(loop_var, EEscape("{p}.first", ("p",), (pair,)).with_type(loop_var.type)),
                    body))
            self.end_statement()
            return
        iterable = self.visit(iterable)
        self.begin_statement()
        self.write("for (", self.visit(loop_var.type, loop_var.id), " : ", iterable, ") ")
        with self.block():
            self.visit(body)
        self.end_statement()

    def visit_EArgMin(self, e):
        raise Exception("argmin is supposed to be handled by simplify_and_optimize")

    def visit_EArgMax(self, e):
        raise Exception("argmax is supposed to be handled by simplify_and_optimize")

    def visit_EListSlice(self, e):
        raise Exception("list slicing is supposed to be handled by simplify_and_optimize")

    def reverse_inplace(self, e : EVar) -> Stm:
        assert isinstance(e.type, TList)
        return SEscape("{indent}std::reverse({e}.begin(), {e}.end());\n", ("e",), (e,))

    def visit_EUnaryOp(self, e):
        op = e.op
        if op in ("-", UOp.Not):
            ee = self.visit(e.e)
            op_str = "!" if op == UOp.Not else op
            return "({op}({ee}))".format(op=op_str, ee=ee)
        elif op == UOp.Reversed:
            v = self.fv(e.type, "v")
            self.declare(v, e.e)
            self.visit(self.reverse_inplace(v))
            return v.id
        elif op in (UOp.Distinct, UOp.AreUnique, UOp.Length, UOp.Sum, UOp.All, UOp.Any, UOp.Exists, UOp.Empty, UOp.The):
            raise Exception("{!r} operator is supposed to be handled by simplify_and_optimize".format(op))
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
                evaluation.construct_value(e.type),
                EEscape("{ee}->val", ("ee",), (ee,)).with_type(e.type)).with_type(e.type))
        return "({ee}.{f})".format(ee=ee, f=e.field_name)

    def visit_ETuple(self, e):
        name = self.typename(e.type)
        args = [self.visit(arg) for arg in e.es]
        return "({}({}))".format(name, ", ".join(args))

    def visit_ETupleGet(self, e):
        if isinstance(e.e, ETuple):
            return self.visit(e.e.es[e.index])
        return self.visit_EGetField(EGetField(e.e, "_{}".format(e.index)))

    def visit_ECall(self, e):
        args = [self.visit(a) for a in e.args]
        if e.func in self.funcs:
            f = self.funcs[e.func]
            return "({})".format(f.body_string.format(**{ arg: "({})".format(val) for (arg, _), val in zip(f.args, args) }))
        else:
            raise Exception("unknown function {}".format(repr(e.func)))

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

    def visit_EMove(self, e):
        return "std::move(" + self.visit(e.e) + ")"

    def visit_ETreeMultisetPeek(self, e):
        return self.visit(ECond(ELt(e.index, EEscape("{xs}.size()", ("xs",), (e.e,))).with_type(BOOL),
                                EEscape("*std::next({xs}.begin(), {i})", ("xs", "i"), (e.e, e.index)).with_type(e.type),
                                evaluation.construct_value(e.type)).with_type(e.type))

    def visit_SErase(self, s):
        return self.visit(SEscape("{indent}{target}.erase({x});", ("target", "x"), (s.target, s.x)))

    def visit_SInsert(self, s):
        return self.visit(SEscape("{indent}{target}.insert({x});", ("target", "x"), (s.target, s.x)))

    def declare(self, v : EVar, initial_value : Exp = None):
        assert hasattr(v, "type"), repr(v)
        if initial_value is not None:
            iv = self.visit(initial_value)
            self.write_stmt(self.visit(v.type, v.id), " = ", iv, ";")
        else:
            self.write_stmt(self.visit(v.type, v.id), ";")

    def visit_SAssign(self, s):
        value = self.visit(s.rhs)
        self.write_stmt(self.visit(s.lhs), " = ", value, ";")

    def visit_SDecl(self, s):
        var = s.var
        assert isinstance(var, EVar)
        if not hasattr(var, "type"):
            # This should not be necessary, but it guards against sloppiness
            # elsewhere.
            var = shallow_copy(var).with_type(s.val.type)
        return self.declare(var, s.val)

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
        if e.cond == ETRUE:
            return self.visit(e.then_branch)
        elif e.cond == EFALSE:
            return self.visit(e.else_branch)
        v = self.fv(e.type, "v")
        self.declare(v)
        self.visit(SIf(e.cond, SAssign(v, e.then_branch), SAssign(v, e.else_branch)))
        return v.id

    def visit_SReturn(self, ret):
        e = self.visit(ret.e)
        self.write_stmt("return ", e, ";")

    def visit_SCall(self, call):
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
            raise NotImplementedError("unknown target type {} in {}".format(pprint(call.target.type), pprint(call)))

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

                # TODO: sort fields by size descending for better packing
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
            return self.define_type(toplevel_name, TRecord(tuple(("_{}".format(i), t.ts[i]) for i in range(len(t.ts)))), name, sharing)
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

    def compute_hash_scalar(self, e: Exp) -> Exp:
        return EEscape("{hasher}()({{e}})".format(hasher=self._hasher(e.type)), ("e",), (e,)).with_type(INT)

    def compute_hash_1(self, hc: Exp, e : Exp) -> Stm:
        if is_scalar(e.type):
            return SAssign(hc, self.compute_hash_scalar(e))
        elif isinstance(e.type, TArray):
            x = fresh_var(e.type.elem_type, "x")
            s = SSeq(SAssign(hc, ZERO.with_type(hc.type)),
                     SForEach(x, e,
                         SAssign(hc, EEscape("({hc} * 31) ^ ({h})", ("hc", "h"),
                                             (hc, self.compute_hash_scalar(x))).with_type(INT))))
            return s
        else:
            raise NotImplementedError("can't compute hash for type {}".format(e.type))

    def compute_hash(self, fields : [Exp]) -> Stm:
        hc = self.fv(INT, "hash_code")
        h = self.fv(INT, "hash_code")
        s = SSeq(SDecl(hc, ENum(0).with_type(hc.type)),
                 SDecl(h, ENum(0).with_type(h.type)))
        for f in fields:
            s = seq([s,
                     self.compute_hash_1(h, f),
                     SAssign(hc,
                        EEscape("({hc} * 31) ^ ({h})", ("hc", "h"), (hc, h)).with_type(INT))])
        s = SSeq(s, SEscape("{indent}return {e};\n", ("e",), (hc,)))
        return s

    def visit_ESingleton(self, e):
        value = self.visit(e.e)
        return self.visit(e.type, "") + " { " + value + " }"

    @typechecked
    def visit_Spec(self, spec : Spec, state_exps : { str : Exp }, sharing, abstract_state=()):
        self.state_exps = state_exps
        self.funcs = { f.name: f for f in spec.extern_funcs }
        self.queries = { q.name: q for q in spec.methods if isinstance(q, Query) }
        self.vars = set(e.id for e in all_exps(spec) if isinstance(e, EVar))

        self.write("#pragma once\n")
        self.write("#include <algorithm>\n")
        self.write("#include <set>\n")
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
                    stm = simplify_and_optimize(SAssign(EVar(name).with_type(t), initial_value))
                    self.visit(stm)
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
                        self.visit(simplify_and_optimize(SAssign(EVar(name).with_type(t), initial_value)))
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

    def visit_ENull(self, e):
        return "nullptr"