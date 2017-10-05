from collections import defaultdict
from datetime import datetime
import itertools
import threading
from functools import lru_cache

import z3

from cozy.target_syntax import *
from cozy.syntax_tools import pprint, free_vars, free_funcs
from cozy.common import declare_case, fresh_name, Visitor, FrozenDict, typechecked, extend
from cozy import evaluation
from cozy.opts import Option

save_solver_testcases = Option("save-solver-testcases", str, "", metavar="PATH")

class SolverReportedUnknown(Exception):
    pass

class ModelValidationError(Exception):
    pass

TReal = declare_case(Type, "TReal", [])
REAL = TReal()

@typechecked
def ite(ty : Type, cond : z3.AstRef, then_branch, else_branch):
    ctx = cond.ctx
    assert isinstance(ctx, z3.Context)
    if decideable(ty):
        return z3.If(cond, then_branch, else_branch, ctx)
    elif isinstance(ty, TBag):
        assert isinstance(then_branch, tuple)
        assert isinstance(else_branch, tuple)
        # print("CONSTRUCTING SYMBOLIC UNION [cond=({})]".format(cond))
        # print(" ---> {}".format(then_branch))
        # print(" ---> {}".format(else_branch))
        then_mask, then_elems = then_branch
        else_mask, else_elems = else_branch
        maxlen = max(len(then_mask), len(else_mask))
        mask = []
        elems = []
        ncond = z3.Not(cond, ctx)
        for i in range(maxlen):
            if i < len(then_mask) and i < len(else_mask):
                mask.append(z3.If(cond, then_mask[i], else_mask[i], ctx))
                elems.append(ite(ty.t, cond, then_elems[i], else_elems[i]))
            elif i < len(then_mask):
                # print("ctx              = {}".format(ctx))
                # print("cond.ctx         = {}".format(cond.ctx_ref()))
                # print("then_mask[i].ctx = {}".format(then_mask[i].ctx_ref()))
                mask.append(z3.And(cond, then_mask[i], ctx))
                elems.append(then_elems[i])
            else:
                assert i < len(else_mask)
                mask.append(z3.And(ncond, else_mask[i], ctx))
                elems.append(else_elems[i])
        return (mask, elems)
    elif isinstance(ty, THandle):
        h1, v1 = then_branch
        h2, v2 = else_branch
        return (z3.If(cond, h1, h2, ctx), ite(ty.value_type, cond, v1, v2))
    elif isinstance(ty, TRecord):
        return { f : ite(t, cond, then_branch[f], else_branch[f]) for (f, t) in ty.fields }
    elif isinstance(ty, TTuple):
        return tuple(ite(t, cond, v1, v2) for (v1, v2, t) in zip(then_branch, else_branch, ty.ts))
    elif isinstance(ty, TMap):
        ncond = z3.Not(cond, ctx)
        def1, map1 = then_branch["default"], then_branch["mapping"]
        def2, map2 = else_branch["default"], else_branch["mapping"]
        mapping = []
        maxlen = max(len(map1), len(map2))
        for i in range(maxlen):
            if i < len(map1) and i < len(map2):
                m1, k1, v1 = map1[i]
                m2, k2, v2 = map2[i]
                mapping.append((
                    ite(BOOL, cond, m1, m2),
                    ite(ty.k, cond, k1, k2),
                    ite(ty.v, cond, v1, v2)))
            elif i < len(map1):
                m1, k1, v1 = map1[i]
                mapping.append((
                    z3.And(cond, m1, ctx),
                    k1,
                    v1))
            else:
                assert i < len(map2)
                m2, k2, v2 = map2[i]
                mapping.append((
                    z3.And(ncond, m2, ctx),
                    k2,
                    v2))

        return {
            "default": ite(ty.v, cond, def1, def2),
            "mapping": mapping }
    elif isinstance(ty, TMaybe):
        p1, v1 = then_branch
        p2, v2 = else_branch
        return (
            z3.If(cond, p1, p2),
            ite(ty.t, cond, v1, v2))
    else:
        raise NotImplementedError(pprint(ty))

class ToZ3(Visitor):
    def __init__(self, z3ctx, z3solver):
        self.ctx = z3ctx
        self.solver = z3solver
        self.int_zero = z3.IntVal(0, self.ctx)
        self.int_one  = z3.IntVal(1, self.ctx)
        self.true = z3.BoolVal(True, self.ctx)
        self.false = z3.BoolVal(False, self.ctx)
        self.handle_vars = []
    def distinct(self, t, *values):
        if len(values) <= 1:
            return z3.BoolVal(True, self.ctx)
        return z3.And(
            self.distinct(t, values[1:]),
            *[z3.Not(self.eq(t, values[0], v1, {}), self.ctx) for v1 in values[1:]],
            self.ctx)
    def lt(self, t, e1, e2, env, deep=False):
        if decideable(t):
            return e1 < e2
        else:
            raise NotImplementedError()
    def gt(self, t, e1, e2, env, deep=False):
        if decideable(t):
            return e1 > e2
        else:
            raise NotImplementedError()
    def eq(self, t, e1, e2, env, deep=False):
        if decideable(t):
            assert isinstance(e1, z3.AstRef), "{}".format(repr(e1))
            assert isinstance(e2, z3.AstRef), "{}".format(repr(e2))
            return e1 == e2
        elif isinstance(t, TMaybe):
            m1, v1 = e1
            m2, v2 = e2
            return z3.And(
                m1 == m2,
                z3.Implies(m1, self.eq(t.t, v1, v2, env, deep=deep), self.ctx),
                self.ctx)
        elif isinstance(t, TBag) or isinstance(t, TSet):
            elem_type = t.t
            lhs_mask, lhs_elems = e1
            rhs_mask, rhs_elems = e2

            # n = max(len(lhs_elems), len(rhs_elems))

            # lengths equal... might not be necessary
            e1len = self.len_of(e1)
            e2len = self.len_of(e2)
            conds = []
            conds.append(e1len == e2len)

            lhs_counts = [ (x, self.count_in(elem_type, e1, x, env, deep=deep)) for x in lhs_elems ]
            for x, count in lhs_counts:
                conds.append(count == self.count_in(elem_type, e2, x, env, deep=deep))

            rhs_counts = [ (x, self.count_in(elem_type, e1, x, env, deep=deep)) for x in rhs_elems ]
            for x, count in rhs_counts:
                conds.append(count == self.count_in(elem_type, e1, x, env, deep=deep))

            if deep:
                # TODO: the(e1) == the(e2)
                pass

            return z3.And(*conds, self.ctx)
        elif isinstance(t, TMap):
            conds = [self.eq(t.v, e1["default"], e2["default"], env, deep=deep)]
            def map_keys(m):
                return ([mask for (mask, k, v) in m["mapping"]], [k for (mask, k, v) in m["mapping"]])
            e1keys = map_keys(e1)
            e2keys = map_keys(e2)
            for (mask, k, v) in e1["mapping"]:
                conds.append(z3.Implies(mask, z3.And(self.is_in(t.k, e2keys, k, env), self.eq(t.v, self._map_get(t, e1, k, env), self._map_get(t, e2, k, env), env, deep=deep), self.ctx), self.ctx))
            for (mask, k, v) in e2["mapping"]:
                conds.append(z3.Implies(mask, z3.And(self.is_in(t.k, e1keys, k, env), self.eq(t.v, self._map_get(t, e1, k, env), self._map_get(t, e2, k, env), env, deep=deep), self.ctx), self.ctx))
            return z3.And(*conds, self.ctx)
        elif isinstance(t, THandle):
            h1, val1 = e1
            h2, val2 = e2
            res = h1 == h2
            if deep:
                res = z3.And(res, self.eq(t.value_type, val1, val2, env, deep=deep), self.ctx)
            return res
        elif isinstance(t, TRecord):
            conds = [self.eq(tt, e1[f], e2[f], env, deep=deep) for (f, tt) in t.fields]
            return z3.And(*conds, self.ctx)
        elif isinstance(t, TTuple):
            conds = [self.eq(t, x, y, env, deep=deep) for (t, x, y) in zip(t.ts, e1, e2)]
            return z3.And(*conds, self.ctx)
        else:
            raise NotImplementedError(t)
    def count_in(self, t, bag, x, env, deep=False):
        """
        t - type of elems in bag
        bag - a bag
        x - elem
        env - environment

        returns # of times x appears in bag
        """
        bag_mask, bag_elems = bag
        l = self.int_zero
        for i in range(len(bag_elems)):
            l = z3.If(z3.And(bag_mask[i], self.eq(t, x, bag_elems[i], env, deep=deep), self.ctx), self.int_one, self.int_zero, ctx=self.ctx) + l
        return l
    def is_in(self, t, bag, x, env, deep=False):
        """
        t - type of elems in bag
        bag - a bag
        x - elem
        env - environment

        returns true if x is in the bag
        """
        bag_mask, bag_elems = bag
        conds = [
            z3.And(mask, self.eq(t, x, elem, env, deep=deep), self.ctx)
            for (mask, elem) in zip(bag_mask, bag_elems)]
        return z3.Or(*conds, self.ctx)
    def len_of(self, val):
        bag_mask, bag_elems = val
        l = self.int_zero
        for i in range(len(bag_elems)):
            l = z3.If(bag_mask[i], self.int_one, self.int_zero, ctx=self.ctx) + l
        return l
    def visit_TInt(self, t):
        return z3.IntSort(self.ctx)
    def visit_TLong(self, t):
        return z3.IntSort(self.ctx)
    def visit_TString(self, t):
        return z3.IntSort(self.ctx)
    def visit_TNative(self, t):
        return z3.IntSort(self.ctx)
    def visit_TBool(self, t):
        return z3.BoolSort(self.ctx)
    def visit_Type(self, t):
        raise NotImplementedError(t)
    def visit_EVar(self, v, env):
        return env[v.id]
    def visit_ENum(self, n, env):
        if n.type in (INT, LONG):
            return z3.IntVal(n.val, self.ctx)
        raise NotImplementedError(n.type)
    def visit_EStr(self, s, env):
        if s.val == "":
            return self.int_zero
        raise NotImplementedError("cannot encode string literal {}".format(repr(s.val)))
    def visit_EBool(self, b, env):
        return z3.BoolVal(b.val, self.ctx)
    def visit_EEmptyList(self, e, env):
        return ([], [])
    def visit_ESingleton(self, e, env):
        return ([z3.BoolVal(True, self.ctx)], [self.visit(e.e, env)])
    def visit_EHandle(self, e, env):
        return (self.visit(e.addr, env), self.visit(e.value, env))
    def visit_ENull(self, e, env):
        return (self.false, self.mkval(e.type.t))
    def visit_EJust(self, e, env):
        return (self.true, self.visit(e.e, env))
    def visit_ELet(self, e, env):
        return self.apply(e.f, self.visit(e.e, env), env)
    def visit_ECall(self, call, env):
        args = [self.visit(x, env) for x in call.args]
        return env[call.func](*args)
    def visit_EEnumEntry(self, e, env):
        return z3.IntVal(e.type.cases.index(e.name), self.ctx)
    def visit_ENative(self, e, env):
        return self.visit(e.e, env)
    def visit_ETuple(self, e, env):
        return tuple(self.visit(ee, env) for ee in e.es)
    def visit_ETupleGet(self, e, env):
        return self.visit(e.e, env)[e.n]
    def visit_EAlterMaybe(self, e, env):
        mask, val = self.visit(e.e, env)
        return mask, self.apply(e.f, val, env)
    def visit_EFlatMap(self, e, env):
        mask, elems = self.visit(EMap(e.e, e.f).with_type(TBag(e.f.body.type)), env)
        res_mask = []
        res_elems = []
        for m, es in zip(mask, elems):
            sub_mask, sub_elems = es
            for mm, ee in zip(sub_mask, sub_elems):
                res_mask.append(z3.And(m, mm, self.ctx))
                res_elems.append(ee)
        return (res_mask, res_elems)
    def visit_ECond(self, e, env):
        cond = self.visit(e.cond, env)
        then_branch = self.visit(e.then_branch, env)
        else_branch = self.visit(e.else_branch, env)
        return ite(e.type, cond, then_branch, else_branch)
    def distinct_bag_elems(self, bag, elem_type, env):
        mask, elems = bag
        if elems:
            rest_mask, rest_elems = self.raw_filter(
                self.distinct_bag_elems((mask[1:], elems[1:]), elem_type, env),
                lambda x: z3.Implies(mask[0], z3.Not(self.eq(elem_type, elems[0], x, env), self.ctx), self.ctx))
            return ([mask[0]] + rest_mask, [elems[0]] + rest_elems)
        else:
            return bag
    def visit_EUnaryOp(self, e, env):
        if e.op == UOp.Not:
            return z3.Not(self.visit(e.e, env), ctx=self.ctx)
        elif e.op == UOp.Sum:
            bag = self.visit(e.e, env)
            bag_mask, bag_elems = bag
            sum = self.int_zero
            for i in range(len(bag_elems)):
                sum = z3.If(bag_mask[i], bag_elems[i], self.int_zero, ctx=self.ctx) + sum
            return sum
        elif e.op == UOp.Length:
            v = EVar("v").with_type(e.e.type.t)
            return self.visit(EUnaryOp(UOp.Sum, EMap(e.e, ELambda(v, ONE)).with_type(TBag(INT))).with_type(e.type), env)
        elif e.op == UOp.AreUnique:
            def is_unique(bag):
                bag_mask, bag_elems = bag
                rest = (bag_mask[1:], bag_elems[1:])
                if bag_elems:
                    return z3.And(
                        z3.Implies(bag_mask[0], z3.Not(self.is_in(e.e.type.t, rest, bag_elems[0], env), self.ctx), self.ctx),
                        is_unique(rest),
                        self.ctx)
                else:
                    return self.true
            return is_unique(self.visit(e.e, env))
        elif e.op == UOp.Empty:
            mask, elems = self.visit(e.e, env)
            return z3.Not(z3.Or(*mask, self.ctx), self.ctx)
        elif e.op == UOp.Exists:
            mask, elems = self.visit(e.e, env)
            return z3.Or(*mask, self.ctx)
        elif e.op == UOp.All:
            mask, elems = self.visit(e.e, env)
            return z3.And(*[z3.Implies(m, e, self.ctx) for (m, e) in zip(mask, elems)], self.ctx)
        elif e.op == UOp.Any:
            mask, elems = self.visit(e.e, env)
            return z3.Or(*[z3.And(m, e, self.ctx) for (m, e) in zip(mask, elems)], self.ctx)
        elif e.op == UOp.Distinct:
            elem_type = e.type.t
            return self.distinct_bag_elems(self.visit(e.e, env), elem_type, env)
        elif e.op == UOp.Length:
            return self.len_of(self.visit(e.e, env))
        elif e.op == UOp.The:
            assert isinstance(e.type, TMaybe)
            t = e.type.t
            bag = self.visit(e.e, env)
            mask, elems = bag
            exists = z3.Or(*mask, self.ctx)
            elem = self.mkval(t)
            for (m, e) in reversed(list(zip(mask, elems))):
                elem = ite(t, m, e, elem)
            return (exists, elem)
        elif e.op == "-":
            return -self.visit(e.e, env)
        else:
            raise NotImplementedError(e.op)
    def _optimal(self, e, env, cmp):
        keytype = e.f.body.type
        mask, elems = self.visit(e.e, env)

        if not elems:
            return self.mkval(e.type)

        # print(pprint(e))

        # 1st pass: find the best key
        first = True
        bestkey = None
        legal = self.false
        keyelems = [self.apply(e.f, x, env) for x in elems]
        for m, key in reversed(list(zip(mask, keyelems))):
            if first:
                bestkey = key
                first = False
                legal = m
            else:
                bestkey = ite(keytype,
                    z3.Or(z3.And(m, cmp(keytype, key, bestkey, env), self.ctx), z3.Not(legal, self.ctx), self.ctx),
                    key,
                    bestkey)
                legal = z3.Or(m, legal, self.ctx)
        # print(" -> bestkey={}".format(bestkey))

        # 2nd pass: find the first elem having that key
        first = True
        res = None
        legal = self.false
        for m, key, x in reversed(list(zip(mask, keyelems, elems))):
            if first:
                res = x
                first = False
                legal = m
            else:
                res = ite(e.type,
                    z3.Or(z3.And(m, self.eq(keytype, key, bestkey, env), self.ctx), z3.Not(legal, self.ctx), self.ctx),
                    x,
                    res)
                legal = z3.Or(m, legal, self.ctx)
        # print(" -> res={}".format(res))

        return ite(e.type, legal, res, self.mkval(e.type))
    def visit_EArgMin(self, e, env):
        return self._optimal(e, env, self.lt)
    def visit_EArgMax(self, e, env):
        return self._optimal(e, env, self.gt)
    def visit_EWithAlteredValue(self, e, env):
        id, val = self.visit(e.handle, env)
        return (id, self.visit(e.new_value, env))
    def visit_EGetField(self, e, env):
        r = self.visit(e.e, env)
        if isinstance(e.e.type, THandle):
            assert e.f == "val"
            h, val = r
            return val
        else:
            return r[e.f]
    def remove_one(self, bag_type, bag, elem, env):
        masks, elems = bag
        if not masks:
            return bag
        rest_masks, rest_elems = self.remove_one(bag_type, (masks[1:], elems[1:]), elem, env)
        return ite(bag_type, z3.And(masks[0], self.eq(bag_type.t, elems[0], elem, env), self.ctx),
            (masks[1:], elems[1:]),
            ([masks[0]] + rest_masks, [elems[0]] + rest_elems))
    def remove_all(self, bag_type, bag, to_remove, env):
        masks, elems = to_remove
        if not masks:
            return bag
        rest = masks[1:], elems[1:]
        return ite(bag_type, masks[0],
            self.remove_all(bag_type, self.remove_one(bag_type, bag, elems[0], env), rest, env),
            self.remove_all(bag_type, bag, rest, env))
    def visit_EBinOp(self, e, env):
        # optimization: x in (distinct y) --> x in y
        # ("distinct" is very expensive for the solver)
        if e.op == BOp.In and isinstance(e.e2, EUnaryOp) and e.e2.op == UOp.Distinct:
            return self.visit(EIn(e.e1, e.e2.e), env)

        # normal path
        v1 = self.visit(e.e1, env)
        v2 = self.visit(e.e2, env)
        if e.op == BOp.And:
            return z3.And(v1, v2, self.ctx)
        elif e.op == BOp.Or:
            return z3.Or(v1, v2, self.ctx)
        elif e.op == "==":
            return self.eq(e.e1.type, v1, v2, env)
        elif e.op == "===":
            return self.eq(e.e1.type, v1, v2, env, deep=True)
        elif e.op == ">":
            return self.gt(e.e1.type, v1, v2, env)
        elif e.op == "<":
            return self.lt(e.e1.type, v1, v2, env)
        elif e.op == ">=":
            return v1 >= v2
        elif e.op == "<=":
            return v1 <= v2
        elif e.op == "*":
            return v1 * v2
        elif e.op == "+":
            if isinstance(e.type, TBag):
                return (v1[0] + v2[0], v1[1] + v2[1])
            elif isinstance(e.type, TSet):
                return self.visit(EUnaryOp(UOp.Distinct, EBinOp(e.e1, "+", e.e2).with_type(TBag(e.type.t))).with_type(TBag(e.type.t)), env)
            elif isinstance(e.type, TInt):
                return v1 + v2
            else:
                raise NotImplementedError(e.type)
        elif e.op == "-":
            if isinstance(e.type, TBag) or isinstance(e.type, TSet):
                return self.remove_all(e.type, v1, v2, env)
            return v1 - v2
        elif e.op == BOp.In:
            return self.is_in(e.e1.type, v2, v1, env)
        else:
            raise NotImplementedError(e.op)
    def visit_EListComprehension(self, e, env):
        x = self.visit_clauses(e.clauses, e.e, env)
        # print("{} ==> {}".format(pprint(e), x))
        return self.visit_clauses(e.clauses, e.e, env)
    def visit_EMap(self, e, env):
        bag_mask, bag_elems = self.visit(e.e, env)
        res_elems = []
        for x in bag_elems:
            res_elems.append(self.apply(e.f, x, env))
        return bag_mask, res_elems
    def do_filter(self, bag, p, env):
        return self.raw_filter(bag, lambda x: self.apply(p, x, env))
    def raw_filter(self, bag, p):
        bag_mask, bag_elems = bag
        res_mask = []
        for mask, x in zip(bag_mask, bag_elems):
            res_mask.append(z3.And(mask, p(x), self.ctx))
        return res_mask, bag_elems
    def visit_EFilter(self, e, env):
        return self.do_filter(self.visit(e.e, env), e.p, env)
    def visit_EMakeMap(self, e, env):
        bag = self.visit(e.e, env)
        bag_mask, bag_elems = bag
        ks = [ self.apply(e.key, x, env) for x in bag_elems ]
        x = EVar(fresh_name()).with_type(e.e.type.t)
        m = {"mapping": [(self.true, k, self.apply(
                e.value,
                self.raw_filter(bag, lambda x: self.eq(e.key.body.type, self.apply(e.key, x, env), k, env)),
                env)) for k in ks],
            "default": self.apply(e.value, ([], []), env)}
        return m
    def visit_EMakeMap2(self, e, env):
        bag_mask, bag_elems = self.visit(e.e, env)
        keys = zip(bag_mask, bag_elems)
        return {
            "mapping": [(mask, key, self.apply(e.value, key, env)) for (mask, key) in keys],
            "default": self.mkval(e.type.v) }
    def visit_EMapKeys(self, e, env):
        m = self.visit(e.e, env)
        d = m["default"]
        m = m["mapping"]
        bag_mask = [mask for (mask, k, v) in m]
        bag_elems = [k for (mask, k, v) in m]
        return self.distinct_bag_elems((bag_mask, bag_elems), e.type.t, env)
    def visit_EMakeRecord(self, e, env):
        return { f:self.visit(v, env) for (f, v) in e.fields }
    def _map_get(self, map_type, map, key, env):
        res = map["default"]
        # print("map get {} on {}".format(key, map))
        for (mask, k, v) in map["mapping"]:
            # print("   k   = {}".format(repr(k)))
            # print("   key = {}".format(repr(key)))
            # print("   v   = {}".format(repr(v)))
            # print("   res = {}".format(repr(res)))
            res = ite(map_type.v, z3.And(mask, self.eq(map_type.k, k, key, env), self.ctx), v, res)
        return res
    def visit_EMapGet(self, e, env):
        map = self.visit(e.map, env)
        key = self.visit(e.key, env)
        return self._map_get(e.map.type, map, key, env)
    def visit_EApp(self, e, env):
        return self.apply(e.f, self.visit(e.arg, env), env)
    def apply(self, lam : ELambda, arg : object, env):
        with extend(env, lam.arg.id, arg):
            return self.visit(lam.body, env)
    def visit_clauses(self, clauses, e, env):
        if not clauses:
            return [True], [self.visit(e, env)]
        c = clauses[0]
        if isinstance(c, CCond):
            bag_mask, bag_elems = self.visit_clauses(clauses[1:], e, env)
            res_mask = []
            for i in range(len(bag_elems)):
                incl_this = z3.And(bag_mask[i], self.visit(c.e, env), self.ctx)
                res_mask += [incl_this]
            return res_mask, bag_elems
        elif isinstance(c, CPull):
            bag_mask, bag_elems = self.visit(c.e, env)
            res_mask, res_elems = [], []
            for i in range(len(bag_elems)):
                incl_this = bag_mask[i]
                env2 = dict(env)
                env2[c.id] = bag_elems[i]
                bag2_mask, bag2_elems = self.visit_clauses(clauses[1:], e, env2)
                res_mask += [z3.And(incl_this, bit, self.ctx) for bit in bag2_mask]
                res_elems += bag2_elems
            return res_mask, res_elems
    def visit_EStateVar(self, e, env):
        return self.visit(e.e, env)
    def visit_Exp(self, e, *args):
        raise NotImplementedError("toZ3({})".format(e))
    def visit_AstRef(self, e, env):
        """AstRef is the Z3 AST node type"""
        return e
    def visit_bool(self, e, env):
        return z3.BoolVal(e, self.ctx)
    def visit(self, e, *args):
        try:
            return super().visit(e, *args)
        except:
            print("failed to convert {}".format(pprint(e)))
            raise

    def mkval(self, type):
        """
        Create an arbitrary value of the given type. Guaranteed to agree with
        cozy.evaluation.mkval(type).
        """
        return self.unreconstruct(evaluation.mkval(type), type)

    def unreconstruct(self, value, type):
        """Converts reconstructed value back to a Z3 value"""
        ctx = self.ctx
        if type == INT or type == LONG:
            return z3.IntVal(value, ctx)
        elif isinstance(type, TBool):
            return self.true if value else self.false
        elif isinstance(type, TBag):
            masks = [self.true for v in value]
            values = [self.unreconstruct(v, type.t) for v in value]
            return (masks, values)
        elif isinstance(type, TMap):
            return {
                "mapping": [(self.true, self.unreconstruct(k, type.k), self.unreconstruct(v, type.v)) for (k, v) in value.items()],
                "default": self.unreconstruct(value.default, type.v) }
        elif isinstance(type, TEnum):
            return z3.IntVal(type.cases.index(value), ctx)
        elif isinstance(type, TNative):
            return z3.IntVal(value[1], ctx)
        elif isinstance(type, THandle):
            return (z3.IntVal(value[0], ctx), self.unreconstruct(value[1], type.value_type))
        elif isinstance(type, TTuple):
            return tuple(self.unreconstruct(v, t) for (v, t) in zip(value, type.ts))
        elif isinstance(type, TRecord):
            return { f:self.unreconstruct(value[f], t) for (f, t) in type.fields }
        elif isinstance(type, TMaybe):
            exists = value.obj is not None
            return (self.unreconstruct(exists, BOOL), self.unreconstruct(value.obj, type.t) if exists else self.mkval(type.t))
        elif isinstance(type, TString):
            if all(c == "a" for c in value):
                return z3.IntVal(len(value), ctx)
            raise NotImplementedError((type, value))
        else:
            raise NotImplementedError(type)

    def mkvar(self, collection_depth, type):
        ctx = self.ctx
        solver = self.solver
        if type == INT or type == LONG or isinstance(type, TNative):
            return z3.Int(fresh_name(), ctx=ctx)
        elif type == REAL:
            return z3.Real(fresh_name(), ctx=ctx)
        elif type == STRING:
            i = z3.Int(fresh_name(), ctx=ctx)
            solver.add(i >= 0)
            return i
        elif type == BOOL:
            return z3.Bool(fresh_name(), ctx=ctx)
        elif isinstance(type, TEnum):
            ncases = len(type.cases)
            n = z3.Int(fresh_name(), ctx=ctx)
            solver.add(n >= 0)
            solver.add(n < ncases)
            return n
        elif isinstance(type, TMaybe):
            return (self.mkvar(collection_depth, BOOL), self.mkvar(collection_depth, type.t))
        elif isinstance(type, TSet):
            res = self.mkvar(collection_depth, TBag(type.t))
            mask, elems = res
            for i in range(1, len(mask)):
                solver.add(z3.Implies(mask[i], self.distinct(type.t, *(elems[:(i+1)])), ctx))
            return res
        elif isinstance(type, TBag):
            mask = [self.mkvar(collection_depth, BOOL) for i in range(collection_depth)]
            elems = [self.mkvar(collection_depth, type.t) for i in range(collection_depth)]
            # symmetry breaking
            for i in range(len(mask) - 1):
                solver.add(z3.Implies(mask[i], mask[i+1], ctx))
            return (mask, elems)
        elif isinstance(type, TMap):
            default = self.mkval(type.v)
            mask = [self.mkvar(collection_depth, BOOL) for i in range(collection_depth)]
            # symmetry breaking
            for i in range(len(mask) - 1):
                solver.add(z3.Implies(mask[i], mask[i+1], ctx))
            return {
                "mapping": [(
                    mask[i],
                    self.mkvar(collection_depth, type.k),
                    self.mkvar(collection_depth, type.v))
                    for i in range(collection_depth)],
                "default":
                    default }
        elif isinstance(type, TRecord):
            # TODO: use Z3 ADTs
            return { field : self.mkvar(collection_depth, t) for (field, t) in type.fields }
        elif isinstance(type, TTuple):
            # TODO: use Z3 ADTs
            return tuple(self.mkvar(collection_depth, t) for t in type.ts)
        elif isinstance(type, THandle):
            h = z3.Int(fresh_name(), ctx)
            v = (h, self.mkvar(collection_depth, type.value_type))
            self.handle_vars.append((type.value_type,) + v)
            return v
        elif isinstance(type, TFunc):
            return z3.Function(fresh_name(),
                *[self.visit(t) for t in type.arg_types],
                self.visit(type.ret_type))
        else:
            raise NotImplementedError(type)

def decideable(t):
    return type(t) in [TInt, TLong, TBool, TString, TEnum, TNative, TReal]

def mkconst(ctx, solver, val):
    if type(val) == int:
        return z3.IntVal(val, ctx)
    elif type(val) == bool:
        return z3.BoolVal(val, ctx)
    elif type(val) == tuple:
        return ([z3.BoolVal(True, ctx) for x in val], [mkconst(ctx, solver, x) for x in val])
    else:
        raise NotImplementedError(repr(val))

_LOCK = threading.Lock()
def satisfy(e, vars = None, funcs = None, collection_depth : int = 2, validate_model : bool = True, model_callback = None, logic : str = None, timeout : float = None):
    start = datetime.now()
    with _LOCK:
        # print("Checking sat (|e|={}); time to acquire lock = {}".format(e.size(), datetime.now() - start))
        start = datetime.now()
        # print("sat? {}".format(pprint(e)))
        assert e.type == BOOL

        ctx = z3.Context()
        solver = z3.Solver(ctx=ctx) if logic is None else z3.SolverFor(logic, ctx=ctx)
        if timeout is not None:
            solver.set("timeout", int(timeout * 1000))
        solver.set("core.validate", validate_model)
        visitor = ToZ3(ctx, solver)

        def reconstruct(model, value, type):
            if type == INT or type == LONG:
                return model.eval(value, model_completion=True).as_long()
            elif type == REAL:
                return model.eval(value, model_completion=True).as_fraction()
            elif isinstance(type, TNative):
                return (type.name, model.eval(value, model_completion=True).as_long())
            elif type == STRING:
                i = model.eval(value, model_completion=True).as_long()
                return "a" * i
            elif type == BOOL:
                return bool(model.eval(value, model_completion=True))
            elif isinstance(type, TMaybe):
                mask, value = value
                mask = reconstruct(model, mask, BOOL)
                value = reconstruct(model, value, type.t)
                return evaluation.Maybe(value if mask else None)
            elif isinstance(type, TBag) or isinstance(type, TSet):
                mask, elems = value
                real_val = []
                for i in range(len(elems)):
                    if reconstruct(model, mask[i], BOOL):
                        real_val.append(reconstruct(model, elems[i], type.t))
                return evaluation.Bag(real_val)
            elif isinstance(type, TMap):
                default = reconstruct(model, value["default"], type.v)
                res = evaluation.Map(type, default)
                for (mask, k, v) in value["mapping"]:
                    # K/V pairs appearing later in value["mapping"] have precedence,
                    # so overwriting here is the correct move.
                    if reconstruct(model, mask, BOOL):
                        k = reconstruct(model, k, type.k)
                        v = reconstruct(model, v, type.v)
                        res[k] = v
                return res
            elif isinstance(type, TEnum):
                val = model.eval(value, model_completion=True).as_long()
                return type.cases[val]
            elif isinstance(type, THandle):
                id, val = value
                id = reconstruct(model, id, INT)
                val = reconstruct(model, val, type.value_type)
                return evaluation.Handle(id, val)
            elif isinstance(type, TRecord):
                res = defaultdict(lambda: None)
                for (field, t) in type.fields:
                    res[field] = reconstruct(model, value[field], t)
                return FrozenDict(res)
            elif isinstance(type, TTuple):
                return tuple(reconstruct(model, v, t) for (v, t) in zip(value, type.ts))
            else:
                raise NotImplementedError(type)

        _env = { }
        if funcs is None:
            funcs = free_funcs(e)
        for f, t in funcs.items():
            _env[f] = visitor.mkvar(collection_depth, t)
        fvs = free_vars(e)
        if vars is None:
            vars = fvs
        else:
            vars = list(vars) + [v for v in fvs if v not in vars]
        for v in vars:
            # print("{} : {}".format(pprint(v), pprint(v.type)))
            _env[v.id] = visitor.mkvar(collection_depth, v.type)
        # print(_env)

        try:
            solver.add(visitor.visit(e, _env))
        except Exception:
            print(" ---> to reproduce: satisfy({e}, vars={vars}, collection_depth={collection_depth}, validate_model={validate_model})".format(
                e=repr(e),
                vars=repr(vars),
                collection_depth=repr(collection_depth),
                validate_model=repr(validate_model)))
            raise

        # Handles implement reference equality... so if the references are the same,
        # the values must be also. TODO: we could eliminiate the need for this by
        # encoding handles as ints plus an uninterpreted "read_value" function for
        # each handle type.
        handle_vars = visitor.handle_vars
        for i in range(len(handle_vars)):
            for j in range(i + 1, len(handle_vars)):
                h1type, h1, v1 = handle_vars[i]
                h2type, h2, v2 = handle_vars[j]
                if h1type == h2type:
                    solver.add(z3.Implies(h1 == h2, visitor.eq(h1type, v1, v2, _env), ctx))

        # print(solver.assertions())
        res = solver.check()
        # print("Checked (res={}); time to encode/solve = {}".format(res, datetime.now() - start))
        if res == z3.unsat:
            return None
        elif res == z3.unknown:
            raise SolverReportedUnknown("z3 reported unknown")
        else:
            model = solver.model()
            # print(model)
            res = { }
            for f, t in funcs.items():
                name = f
                f = _env[name]
                out_type = t.ret_type
                arg_types = t.arg_types
                @lru_cache(maxsize=None)
                def extracted_func(*args):
                    return reconstruct(model, f(*[visitor.unreconstruct(v, t) for (v, t) in zip(args, arg_types)]), out_type)
                res[name] = extracted_func
            for v in vars:
                res[v.id] = reconstruct(model, _env[v.id], v.type)
            if model_callback is not None:
                model_callback(res)
            if validate_model:
                x = evaluation.eval(e, res)
                if x is not True:
                    print("bad example: {}".format(res))
                    print(" ---> formula: {}".format(pprint(e)))
                    print(" ---> got {}".format(repr(x)))
                    print(" ---> model: {}".format(model))
                    print(" ---> assertions: {}".format(solver.assertions()))
                    print(" ---> to reproduce: satisfy({e}, vars={vars}, collection_depth={collection_depth}, validate_model={validate_model})".format(
                        e=repr(e),
                        vars=repr(vars),
                        collection_depth=repr(collection_depth),
                        validate_model=repr(validate_model)))
                    if save_solver_testcases.value:
                        with open(save_solver_testcases.value, "a") as f:
                            f.write("satisfy({e}, vars={vars}, collection_depth={collection_depth}, validate_model={validate_model})".format(
                                e=repr(e),
                                vars=repr(vars),
                                collection_depth=repr(collection_depth),
                                validate_model=repr(validate_model)))
                            f.write("\n")
                    from cozy.syntax_tools import all_exps, equal
                    wq = [(e, _env, res)]
                    while wq:
                        x, solver_env, eval_env = wq.pop()
                        for x in sorted(all_exps(e), key=lambda xx: xx.size()):
                            if all(v.id in eval_env for v in free_vars(x)) and not isinstance(x, ELambda):
                                solver_val = reconstruct(model, visitor.visit(x, solver_env), x.type)
                                v = fresh_name("tmp")
                                eval_env[v] = solver_val
                                eval_val = evaluation.eval(equal(x, EVar(v).with_type(x.type)), eval_env)
                                if not eval_val:
                                    print(" ---> disagreement on {}".format(pprint(x)))
                                    print(" ---> Solver: {}".format(solver_val))
                                    print(" ---> Eval'r: {}".format(evaluation.eval(x, eval_env)))
                                    for v in free_vars(x):
                                        print(" ---> s[{}] = {}".format(v.id, solver_env[v.id]))
                                        print(" ---> e[{}] = {}".format(v.id, eval_env[v.id]))
                                    for i, c in enumerate(x.children()):
                                        if isinstance(c, Exp) and not isinstance(c, ELambda):
                                            print(" ---> solver arg[{}] = {}".format(i, reconstruct(model, visitor.visit(c, solver_env), c.type)))
                                            print(" ---> eval'r arg[{}] = {}".format(i, evaluation.eval(c, eval_env)))
                                    if isinstance(x, EFilter):
                                        smask, selems = visitor.visit(x.e, solver_env)
                                        for (mask, elem) in zip(smask, selems):
                                            if reconstruct(model, mask, BOOL):
                                                # print("recursing on {}".format(elem))
                                                senv = dict(solver_env)
                                                eenv = dict(eval_env)
                                                senv[x.p.arg.id] = elem
                                                eenv[x.p.arg.id] = reconstruct(model, elem, x.type.t)
                                                wq.append((x.p.body, senv, eenv))
                                    break
                    raise ModelValidationError("model validation failed")
            return res

def satisfiable(e, **opts):
    return satisfy(e, **opts) is not None

def valid(e, **opts):
    return satisfy(EUnaryOp("not", e).with_type(BOOL), **opts) is None
