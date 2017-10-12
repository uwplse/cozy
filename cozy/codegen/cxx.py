from collections import OrderedDict
import json

from cozy import common, library, evaluation
from cozy.common import fresh_name
from cozy.target_syntax import *
from cozy.syntax_tools import all_types, fresh_var, subst, free_vars, is_scalar, mk_lambda, alpha_equivalent
from cozy.simplification import simplify

from .misc import *

class CxxPrinter(common.Visitor):

    def __init__(self, use_qhash : bool = False):
        self.types = OrderedDict()
        self.funcs = {}
        self.queries = {}
        self.use_qhash = use_qhash

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

    def visit_THandle(self, t, name):
        return "{} *{}".format(self.typename(t), name)

    def visit_TNativeMap(self, t, name):
        if self.use_qhash:
            return "QHash< {}, {} > {}".format(self.visit(t.k, ""), self.visit(t.v, ""), name)
        else:
            return "std::unordered_map< {}, {} > {}".format(self.visit(t.k, ""), self.visit(t.v, ""), name)

    def visit_TMap(self, t, name):
        return self.visit(t.rep_type(), name)

    def visit_TNativeList(self, t, name):
        return "std::vector< {} > {}".format(self.visit(t.t, ""), name)

    def visit_TNativeSet(self, t, name):
        return "std::unordered_set< {} > {}".format(self.visit(t.t, ""), name)

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
        if cond_setup:
            return "{indent0}for (;;) {{\n{cond_setup}{indent}if ({cond}) break;\n{body}{indent0}}}\n".format(
                indent0=indent,
                indent=indent+INDENT,
                cond_setup=cond_setup,
                cond=cond,
                body=body)
        else:
            return "{indent0}while (!{cond}) {{\n{body}{indent0}}}\n".format(
                indent0=indent,
                cond=cond,
                body=body)

    def visit_SEscapableBlock(self, s, indent):
        return "{body}{label}:\n".format(body=self.visit(s.body, indent), label=s.label)

    def visit_SEscapeBlock(self, s, indent):
        return "{indent}goto {label};\n".format(indent=indent, label=s.label)

    def visit_str(self, s, indent=""):
        return indent + s + "\n"

    def visit_Query(self, q, indent=""):
        if q.visibility != Visibility.Public:
            return ""
        ret_type = q.ret.type
        if isinstance(ret_type, TBag):
            x = EVar(common.fresh_name("x")).with_type(ret_type.t)
            s  = "{indent}template <class F>\n".format(indent=indent)
            s += "{indent}inline void {name} ({args}const F& _callback) const {{\n{body}  }}\n\n".format(
                indent=indent,
                name=q.name,
                args="".join("{}, ".format(self.visit(t, name)) for name, t in q.args),
                body=self.visit(SForEach(x, q.ret, SEscape("{indent}_callback({x});\n", ["x"], [x])), indent=indent+INDENT))
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

    def visit_EEmptyList(self, e, indent=""):
        if isinstance(e.type, library.TNativeList):
            v = fresh_name("empty")
            decl = "{indent}{decl};\n".format(indent=indent, decl=self.visit(e.type, name=v))
            return (decl + self.visit(self.initialize_native_list(EVar(v).with_type(e.type)), indent), v)
        elif isinstance(e.type, library.TNativeSet):
            v = fresh_name("empty")
            decl = "{indent}{decl};\n".format(indent=indent, decl=self.visit(e.type, name=v))
            return (decl + self.visit(self.initialize_native_set(EVar(v).with_type(e.type)), indent), v)
        return self.visit(e.type.make_empty(), indent)

    def native_map_get(self, e, default_value, indent=""):
        (smap, emap) = self.visit(e.map, indent)
        (skey, ekey) = self.visit(e.key, indent)
        if self.use_qhash:
            return (smap + skey, "{}.value({})".format(emap, ekey))
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
        Construct a value of type `t` from the expression `e` and store it in
        lvalue `out`.
        """
        if hasattr(t, "construct_concrete"):
            return t.construct_concrete(e, out)
        elif isinstance(t, library.TNativeList) or type(t) is TBag:
            x = fresh_var(t.t, "x")
            return SSeq(
                self.initialize_native_list(out),
                SForEach(x, e, SCall(out, "add", [x])))
        elif isinstance(t, library.TNativeSet) or type(t) is TSet:
            if isinstance(e, EUnaryOp) and e.op == UOp.Distinct:
                return self.construct_concrete(t, e.e, out)
            x = fresh_var(t.t, "x")
            return SSeq(
                self.initialize_native_set(out),
                SForEach(x, e, SCall(out, "add", [x])))
        elif isinstance(t, library.TNativeMap):
            return SSeq(
                self.initialize_native_map(out),
                self.construct_map(t, e, out))
        elif type(t) in [TBool, TInt, TNative, THandle, TLong, TString, TEnum, TTuple, TRecord]:
            return SEscape("{indent}{lhs} = {rhs};\n", ["lhs", "rhs"], [out, e])
        raise NotImplementedError(t)

    def construct_map(self, t, e, out):
        if isinstance(e, ECond):
            return SIf(e.cond,
                construct_map(t, e.then_branch, out),
                construct_map(t, e.else_branch, out))
        elif isinstance(e, EMakeMap2):
            k = fresh_var(t.k, "k")
            v = fresh_var(t.v, "v")
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
        if isinstance(e.map, EStateVar):
            return self.visit(EMapGet(e.map.e, e.key).with_type(e.type), indent=indent)
        elif isinstance(e.map, EMakeMap2):
            return self.visit(ELet(e.key, mk_lambda(e.key.type, lambda k:
                ECond(EBinOp(k, BOp.In, e.map.e).with_type(BOOL),
                    e.map.value.apply_to(k),
                    evaluation.construct_value(e.map.type.v)).with_type(e.type))).with_type(e.type), indent=indent)
        elif isinstance(e.map, ECond):
            return self.visit(ELet(e.key, mk_lambda(e.key.type, lambda k:
                ECond(e.map.cond,
                    EMapGet(e.map.then_branch, k).with_type(e.type),
                    EMapGet(e.map.else_branch, k).with_type(e.type)).with_type(e.type))).with_type(e.type), indent=indent)
        elif isinstance(e.map, EVar):
            if isinstance(e.map.type, library.TNativeMap):
                return self.native_map_get(
                    e,
                    lambda out: self.construct_concrete(
                        e.map.type.v,
                        evaluation.construct_value(e.map.type.v),
                        out),
                    indent)
            else:
                return self.visit(e.map.type.get_key(e.map, e.key), indent)
        else:
            raise NotImplementedError(type(e.map))

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

    def visit_SMapPut(self, update, indent=""):
        if isinstance(update.map.type, library.TNativeMap):
            msetup, map = self.visit(update.map, indent)
            ksetup, key = self.visit(update.key, indent)
            ref = fresh_var(update.map.type.v, "ref")
            s = "{indent}{decl} = {map}[{key}];\n".format(
                indent=indent,
                map=map,
                key=key,
                decl=self.visit(TRef(ref.type), ref.id))
            return msetup + ksetup + s + self.copy_to(ref, update.value, indent)
        else:
            raise NotImplementedError()

    def visit_SMapDel(self, update, indent=""):
        if isinstance(update.map.type, library.TNativeMap):
            msetup, map = self.visit(update.map, indent)
            ksetup, key = self.visit(update.key, indent)
            s = "{indent}{map}.erase({key});\n".format(
                indent=indent,
                map=map,
                key=key)
            return msetup + ksetup + s
        else:
            raise NotImplementedError()

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

    def visit_EWithAlteredValue(self, e, indent=""):
        # TODO: This isn't quite right.
        # EWithAlteredValue produces a "magic" handle value with the same
        # address as `e.handle`, but a different value at the other side. A
        # correct implementation would be much more complex:
        #  - allocate a new handle A with the appropriate value
        #  - add a note in an auxiliary structure stating that A aliases with
        #    e.handle
        #  - when you check equality of handles, also consult the auxiliary
        #    structure for hidden aliases
        #  - on return from method, free all magic handles mentioned in the
        #    auxiliary structure
        return self.visit(e.handle, indent)

    def _is_concrete(self, e):
        if is_scalar(e.type):
            return True
        elif type(e.type) in [TMap, TSet, TBag]:
            return False
        return True

    def histogram(self, e, indent) -> (str, EVar):
        t = library.TNativeMap(e.type.t, INT)
        hist = fresh_var(t, "hist")
        x = fresh_var(e.type.t)
        val = fresh_var(INT, "val")
        decl = self.visit(t, hist.id)
        s = self.visit(SForEach(x, e,
            SMapUpdate(hist, x, val,
                SAssign(val, EBinOp(val, "+", ONE).with_type(INT)))), indent)
        return ("{}{};\n".format(indent, decl) + self.visit(self.initialize_native_map(hist), indent) + s, hist)

    def _eq(self, e1, e2, indent):
        if (is_scalar(e1.type) or
                (isinstance(e1.type, library.TNativeMap) and isinstance(e2.type, library.TNativeMap)) or
                (isinstance(e1.type, library.TNativeSet) and isinstance(e2.type, library.TNativeSet)) or
                (isinstance(e1.type, library.TNativeList) and isinstance(e2.type, library.TNativeList))):
            return self.visit(EEscape("({e1} == {e2})", ["e1", "e2"], [e1, e2]), indent)
        elif isinstance(e1.type, TSet) and isinstance(e2.type, TSet):
            raise NotImplementedError("set equality")
        elif isinstance(e1.type, TBag) or isinstance(e2.type, TBag):
            setup1, v1 = self.histogram(e1, indent)
            setup2, v2 = self.histogram(e2, indent)
            setup3, res = self._eq(v1, v2, indent)
            return (setup1 + setup2 + setup3, res)
        elif isinstance(e1.type, TMap) or isinstance(e2.type, TMap):
            raise NotImplementedError("map equality")
        else:
            raise NotImplementedError((e1.type, e2.type))

    def visit_EBinOp(self, e, indent=""):
        op = e.op
        if op == "+" and (isinstance(e.e1.type, TBag) or isinstance(e.e1.type, TSet)):
            raise NotImplementedError("adding collections: {}".format(e))
        elif op == "==":
            return self._eq(e.e1, e.e2, indent)
        elif op == BOp.In:
            if isinstance(e.e2.type, TSet):
                if type(e.e2.type) in (TSet, library.TNativeSet):
                    return self.test_set_containment_native(e.e2, e.e1, indent)
                else:
                    return self.visit(e.e2.type.contains(e.e1), indent)
            else:
                t = TBool()
                res = fresh_var(t, "found")
                x = fresh_var(e.e1.type, "x")
                label = fresh_name("label")
                setup = self.visit(seq([
                    SDecl(res.id, EBool(False).with_type(t)),
                    SEscapableBlock(label,
                        SForEach(x, e.e2, SIf(
                            EBinOp(x, "==", e.e1).with_type(BOOL),
                            seq([SAssign(res, EBool(True).with_type(t)), SEscapeBlock(label)]),
                            SNoOp())))]), indent)
                return (setup, res.id)
        elif op == "-" and isinstance(e.type, TBag):
            t = e.type
            if type(t) is TBag:
                t = library.TNativeList(t.t)
            v = fresh_var(t, "v")
            x = fresh_var(t.t, "x")
            stm = self.visit(SForEach(x, e.e2, SCall(v, "remove", [x])), indent)
            return ("{}{};\n".format(indent, self.visit(v.type, v.id)) + self.visit(self.construct_concrete(v.type, e.e1, v), indent) + stm, v.id)
        elif op == BOp.Or:
            (s1, r1) = self.visit(e.e1)
            (s2, r2) = self.visit(e.e2)
            if s2:
                return self.visit(ECond(e.e1, EBool(True), e.e2).with_type(TBool()), indent)
            else:
                return (s1, "({} || {})".format(r1, r2))
        elif op == BOp.And:
            (s1, r1) = self.visit(e.e1)
            (s2, r2) = self.visit(e.e2)
            if s2:
                return self.visit(ECond(e.e1, EBool(True), e.e2).with_type(TBool()), indent)
            else:
                return (s1, "({} && {})".format(r1, r2))
        ce1, e1 = self.visit(e.e1, indent)
        ce2, e2 = self.visit(e.e2, indent)
        return (ce1 + ce2, "({e1} {op} {e2})".format(e1=e1, op=op, e2=e2))

    def test_set_containment_native(self, set : Exp, elem : Exp, indent) -> (str, str):
        return self.visit(EEscape("{set}.find({elem}) != {set}.end()", ["set", "elem"], [set, elem]), indent)

    def for_each(self, iterable : Exp, body, indent="") -> str:
        """Body is function: exp -> stm"""
        if isinstance(iterable, EEmptyList):
            return ""
        elif isinstance(iterable, ESingleton):
            return self.visit(body(iterable.e), indent=indent)
        elif isinstance(iterable, ECond):
            v = fresh_var(iterable.type.t, "v")
            new_body = body(v)
            return self.visit(SIf(iterable.cond,
                SForEach(v, iterable.then_branch, new_body),
                SForEach(v, iterable.else_branch, new_body)), indent=indent)
        elif isinstance(iterable, EMap):
            return self.for_each(
                iterable.e,
                lambda v: body(iterable.f.apply_to(v)),
                indent=indent)
        elif isinstance(iterable, EUnaryOp) and iterable.op == UOp.Distinct:
            tmp = fresh_var(library.TNativeSet(iterable.type.t), "tmp")
            return "".join((
                "{indent}{decl};\n".format(indent=indent, decl=self.visit(tmp.type, tmp.id)),
                self.visit(self.initialize_native_set(tmp), indent),
                # TODO: could get better performance out of single "find or insert" primitive
                self.for_each(iterable.e, lambda x: SIf(
                    ENot(EBinOp(x, BOp.In, tmp).with_type(BOOL)),
                    seq([body(x), SCall(tmp, "add", [x])]),
                    SNoOp()), indent)))
        elif isinstance(iterable, EFilter):
            return self.for_each(iterable.e, lambda x: SIf(iterable.p.apply_to(x), body(x), SNoOp()), indent=indent)
        elif isinstance(iterable, EBinOp) and iterable.op == "+":
            return self.for_each(iterable.e1, body, indent=indent) + self.for_each(iterable.e2, body, indent=indent)
        elif isinstance(iterable, EFlatMap):
            # TODO: properly handle breaks inside body
            # TODO: indents get messed up here
            return self.for_each(EFlatten(EMap(iterable.e, iterable.f).with_type(TBag(iterable.type))).with_type(iterable.type), body, indent)
        elif isinstance(iterable, ECall) and iterable.func in self.queries:
            q = self.queries[iterable.func]
            return self.for_each(subst(q.ret, { a : v for ((a, t), v) in zip(q.args, iterable.args) }), body, indent=indent)
        elif isinstance(iterable, ELet):
            return self.for_each(iterable.f.apply_to(iterable.e), body, indent=indent)
        else:
            x = fresh_var(iterable.type.t, "x")
            if type(iterable.type) in (TBag, library.TNativeList, TSet, library.TNativeSet):
                return self.for_each_native(x, iterable, body(x), indent)
            return self.visit(iterable.type.for_each(x, iterable, body(x)), indent=indent)

    def for_each_native(self, x, iterable, body, indent):
        setup, iterable = self.visit(iterable, indent)
        return "{setup}{indent}for ({decl} : {iterable}) {{\n{body}{indent}}}\n".format(
            indent=indent,
            setup=setup,
            decl=self.visit(x.type, x.id),
            iterable=iterable,
            body=self.visit(body, indent+INDENT))

    def visit_SForEach(self, for_each, indent):
        id = for_each.id
        iter = for_each.iter
        body = for_each.body
        return self.for_each(iter, lambda x: subst(body, {id.id : x}), indent)

    def find_one(self, iterable, indent=""):
        v = fresh_var(iterable.type.t, "v")
        label = fresh_name("label")
        x = fresh_var(iterable.type.t, "x")
        decl = SDecl(v.id, evaluation.construct_value(v.type))
        find = SEscapableBlock(label,
            SForEach(x, iterable, seq([
                SAssign(v, x),
                SEscapeBlock(label)])))
        return (self.visit(seq([decl, find]), indent), v.id)

    def min_or_max(self, op, e, f, indent=""):
        out = fresh_var(e.type.t, "min" if op == "<" else "max")
        first = fresh_var(BOOL, "first")
        x = fresh_var(e.type.t, "x")
        decl1 = SDecl(out.id, evaluation.construct_value(out.type))
        decl2 = SDecl(first.id, T)
        find = SForEach(x, e,
            SIf(EBinOp(
                    first,
                    BOp.Or,
                    EBinOp(f.apply_to(x), op, f.apply_to(out))),
                seq([SAssign(first, F), SAssign(out, x)]),
                SNoOp()))
        return (self.visit(seq([decl1, decl2, find]), indent), out.id)

    def visit_EArgMin(self, e, indent=""):
        return self.min_or_max("<", e.e, e.f, indent)

    def visit_EArgMax(self, e, indent=""):
        return self.min_or_max(">", e.e, e.f, indent)

    def visit_EUnaryOp(self, e, indent):
        op = e.op
        if op == UOp.The:
            return self.find_one(e.e, indent=indent)
        elif op == UOp.Sum:
            type = e.e.type.t
            res = fresh_var(type, "sum")
            x = fresh_var(type, "x")
            setup = self.visit(seq([
                SDecl(res.id, ENum(0).with_type(type)),
                SForEach(x, e.e, SAssign(res, EBinOp(res, "+", x).with_type(type)))]), indent)
            return (setup, res.id)
        elif op == UOp.Empty:
            raise NotImplementedError()
        elif op == UOp.Exists:
            return self.visit(ENot(EUnaryOp(UOp.Empty, e.e).with_type(BOOL)), indent)
        elif op in ("-", UOp.Not):
            ce, ee = self.visit(e.e, indent)
            op_str = "!" if op == UOp.Not else str(op)
            return (ce, "({op}{ee})".format(op=op_str, ee=ee))
        elif op == UOp.Distinct:
            v = fresh_var(e.type, "v")
            stm = self.construct_concrete(e.type, e, v)
            return ("{}{};\n".format(indent, self.visit(e.type, v.id)) + self.visit(stm, indent), v.id)
        else:
            raise NotImplementedError(op)

    def visit_EGetField(self, e, indent=""):
        ce, ee = self.visit(e.e, indent)
        op = "."
        if isinstance(e.e.type, THandle) or isinstance(e.e.type, library.TIntrusiveLinkedList):
            op = "->"
        return (ce, "({ee}{op}{f})".format(ee=ee, op=op, f=e.f))

    def visit_ETuple(self, e, indent=""):
        name = self.typename(e.type)
        setups, args = zip(*[self.visit(arg, indent) for arg in e.es])
        return ("".join(setups), "{}({})".format(name, ", ".join(args)))

    def visit_ETupleGet(self, e, indent=""):
        return self.visit_EGetField(EGetField(e.e, "_{}".format(e.n)), indent)

    def visit_ECall(self, e, indent=""):
        if e.args:
            setups, args = zip(*[self.visit(arg, indent) for arg in e.args])
        else:
            setups, args = ([], [])
        if e.func in self.funcs:
            f = self.funcs[e.func]
            return ("".join(setups), "({})".format(f.body_string.format(**{ arg: val for (arg, _), val in zip(f.args, args) })))
        elif e.func in self.queries:
            q = self.queries[e.func]
            body = subst(q.ret, { q.args[i][0] : EEscape(args[i], (), ()).with_type(q.args[i][1]) for i in range(len(q.args)) })
            setup, res = self.visit(body, indent=indent)
            return ("".join(setups) + setup, res)
        else:
            raise Exception("unknown function {}".format(repr(e.func)))

    def visit_ELet(self, e, indent=""):
        v = fresh_var(e.e.type, "v")
        setup1 = self.visit(SDecl(v.id, e.e), indent=indent)
        setup2, res = self.visit(e.f.apply_to(v), indent=indent)
        return (setup1 + setup2, res)

    def visit_Exp(self, e, indent=""):
        raise NotImplementedError(e)

    def visit_SEscape(self, s, indent=""):
        body = s.body_string
        args = s.args
        if not args:
            return body.format(indent=indent)
        setups, args = zip(*[self.visit(arg, indent) for arg in args])
        return "".join(setups) + body.format(indent=indent, **dict(zip(s.arg_names, args)))

    def visit_EEscape(self, e, indent=""):
        body = e.body_string
        args = e.args
        if not args:
            return ("", body)
        setups, args = zip(*[self.visit(arg, indent) for arg in args])
        return ("".join(setups), "(" + body.format(**dict(zip(e.arg_names, args))) + ")")

    def visit_SNoOp(self, s, indent=""):
        return ""

    def copy_to(self, lhs, rhs, indent=""):
        if isinstance(lhs.type, TBag):
            cl, el = self.visit(lhs, indent)
            x = fresh_var(lhs.type.t, "x")
            # TODO: hacky use of EVar ahead! We need an EEscape, like SEscape
            return cl + self.visit(SForEach(x, rhs, SCall(EVar(el).with_type(lhs.type), "add", [x])), indent=indent)
        else:
            return self.visit(SAssign(lhs, rhs), indent)

    def visit_SAssign(self, s, indent=""):
        if alpha_equivalent(simplify(s.lhs), simplify(s.rhs)):
            return self.visit(SNoOp(), indent)
        stm = self.construct_concrete(s.lhs.type, s.rhs, s.lhs)
        return self.visit(stm, indent)

    def visit_SDecl(self, s, indent=""):
        t = s.val.type
        decl = self.visit(t, s.id)
        return self.visit(seq([
            SEscape("{{indent}}{};\n".format(decl), [], []),
            SAssign(EVar(s.id).with_type(t), s.val)]), indent)

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
        scond = simplify(e.cond)
        if scond == T:
            return self.visit(e.then_branch, indent)
        elif scond == F:
            return self.visit(e.else_branch, indent)
        v = fresh_var(e.type, "v")
        return (
            "{indent}{decl};\n".format(indent=indent, decl=self.visit(v.type, v.id)) +
            self.visit(SIf(e.cond, SAssign(v, e.then_branch), SAssign(v, e.else_branch)), indent),
            v.id)

    def visit_SCall(self, call, indent=""):
        if type(call.target.type) in (library.TNativeList, TBag):
            if call.func == "add":
                setup1, target = self.visit(call.target, indent)
                setup2, arg = self.visit(call.args[0], indent)
                return setup1 + setup2 + "{}{}.push_back({});\n".format(indent, target, arg)
            elif call.func == "remove":
                setup1, target = self.visit(call.target, indent)
                setup2, arg = self.visit(call.args[0], indent)
                it = fresh_name("it")
                return setup1 + setup2 + "{indent}auto {it}(::std::find({target}.begin(), {target}.end(), {arg}));\n{indent}if ({it} != {target}.end()) {target}.erase({it});\n".format(
                    indent=indent,
                    arg=arg,
                    target=target,
                    it=it)
            else:
                raise NotImplementedError(call.func)
        elif type(call.target.type) in (library.TNativeSet, TSet):
            if call.func == "add":
                setup1, target = self.visit(call.target, indent)
                setup2, arg = self.visit(call.args[0], indent)
                return setup1 + setup2 + "{}{}.insert({});\n".format(indent, target, arg)
            elif call.func == "remove":
                setup1, target = self.visit(call.target, indent)
                setup2, arg = self.visit(call.args[0], indent)
                return setup1 + setup2 + "{}{target}.erase({target}.find({}));\n".format(indent, arg, target=target)
            else:
                raise NotImplementedError(call.func)
        f = getattr(call.target.type, "implement_{}".format(call.func))
        stm = f(call.target, call.args)
        return self.visit(stm, indent)

    def nbits(self, t):
        if t == BOOL:
            return 1
        elif isinstance(t, TEnum):
            return common.integer_log2_round_up(len(t.cases))
        else:
            return None

    def declare_field(self, name, type, indent):
        nbits = self.nbits(type)
        bitspec = " : {}".format(nbits) if nbits else ""
        return "{indent}{field_decl}{bitspec};\n".format(
            indent=indent,
            field_decl=self.visit(type, name),
            bitspec=bitspec)

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
                s += self.declare_field(f, ft, indent=indent+INDENT)
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
        elif isinstance(t, TTuple):
            return self.define_type(toplevel_name, TRecord(tuple(("_{}".format(i), t.ts[i]) for i in range(len(t.ts)))), name, indent, sharing);
        else:
            return ""

    def setup_types(self, spec, state_exps, sharing):
        self.types.clear()
        names = { t : name for (name, t) in spec.types }
        for t in all_types(spec):
            if t not in self.types and type(t) in [THandle, TRecord, TTuple, TEnum]:
                name = names.get(t, common.fresh_name("Type"))
                self.types[t] = name

    def visit_Spec(self, spec, state_exps, sharing):
        self.state_exps = state_exps
        self.funcs = { f.name: f for f in spec.extern_funcs }
        self.queries = { q.name: q for q in spec.methods if isinstance(q, Query) }

        s = "#pragma once\n"
        s += "#include <algorithm>\n"
        s += "#include <vector>\n"
        s += "#include <unordered_set>\n"
        if self.use_qhash:
            s += "#include <QHash>\n"
        else:
            s += "#include <unordered_map>\n"
        s += spec.header
        s += "\nclass {} {{\n".format(spec.name)
        s += "public:\n"

        self.setup_types(spec, state_exps, sharing)
        for t, name in self.types.items():
            s += self.define_type(spec.name, t, name, INDENT, sharing)
        s += "protected:\n"
        for name, t in spec.statevars:
            self.statevar_name = name
            s += self.declare_field(name, t, indent=INDENT)
        s += "public:\n"
        s += INDENT + "inline {name}() {{\n".format(name=spec.name)
        for name, t in spec.statevars:
            initial_value = state_exps[name]
            fvs = free_vars(initial_value)
            initial_value = subst(initial_value, {v.id : evaluation.construct_value(v.type) for v in fvs})
            setup = self.construct_concrete(t, initial_value, EVar(name).with_type(t))
            s += self.visit(setup, INDENT + INDENT)
        s += INDENT + "}\n"
        s += INDENT + "{name}(const {name}& other) = delete;\n".format(name=spec.name)
        for op in spec.methods:
            s += self.visit(op, INDENT)
        s += "};\n\n"
        s += spec.footer
        if not s.endswith("\n"):
            s += "\n"
        return s
