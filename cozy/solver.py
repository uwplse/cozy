"""Bounded satisfiability and validity solver for Cozy expressions.

Important functions and classes:
 - satisfy: search for a small model for a boolean expression
 - satisfiable: check whether a small model exists (but do not return it)
 - valid: check whether an expression is valid for all small models
 - IncrementalSolver: a class to efficiently check assertions incrementally
 - ModelCachingSolver: a class that saves models between satisfiability checks
"""

from collections import defaultdict, OrderedDict
from datetime import datetime, timedelta
from functools import lru_cache
import threading

import z3

from cozy.target_syntax import *
from cozy.syntax_tools import BottomUpExplorer, pprint, free_vars, free_funcs, cse, all_exps, purify
from cozy.typecheck import is_collection, is_numeric
from cozy.common import declare_case, fresh_name, Visitor, FrozenDict, typechecked, extend, OrderedSet, make_random_access
from cozy import evaluation
from cozy.opts import Option
from cozy.structures import extension_handler
from cozy.logging import task
from cozy.value_types import Map, Bag, Handle
from cozy.evaluation import eval_bulk
from cozy.contexts import Context

collection_depth_opt = Option("collection-depth", int, 4, metavar="N", description="Bound for bounded verification")
use_quantified_encoding = Option("quantified-encoding", bool, False, description="Allow the use of quantifiers during formula encoding. The resulting formulas are still decideable using Z3's macro_finder option. Enabling this option offloads work from Python to Z3. Generally it harms performance.")

class SolverReportedUnknown(Exception):
    pass

class ModelValidationError(Exception):
    pass

TReal = declare_case(Type, "TReal", [])
REAL = TReal()

# Encoding Cozy-types for Z3.
#   mkvar:   ETRUE -> [z3var]
#   flatten: ETRUE -> obj -> [z3exp]
#   pack:    ETRUE -> [z3exp] -> obj

def break_let(e):
    while isinstance(e, ELet):
        yield (e.body_function.arg, e.e)
        e = e.body_function.body
    yield e

class DetFlatVis(BottomUpExplorer):
    def join(self, x, new_children):
        if is_collection(x) or isinstance(x, TMap) or isinstance(x, TFunc):
            return False
        return all(new_children)
_DET_FLAT_VIS = DetFlatVis().visit
def deterministic_flattenable(t):
    """
    Does self.flatten(t, x) return the same number of expressions no matter
    what `x` is?
    """
    return _DET_FLAT_VIS(t)

def flatten(t, x):
    # MUST agree with pack()
    h = extension_handler(type(t))
    if h is not None:
        yield from flatten(h.encoding_type(t), x)
        return

    if decideable(t):
        yield x
    elif isinstance(t, TTuple):
        for y, tt in zip(x, t.ts):
            yield from flatten(tt, y)
    elif isinstance(t, TRecord):
        for f, tt in t.fields:
            yield from flatten(tt, x[f])
    elif isinstance(t, THandle):
        yield from flatten(INT, x[0])
        yield from flatten(t.value_type, x[1])
    elif is_collection(t):
        yield len(x[0])
        for mask, elem in zip(*x):
            yield from flatten(BOOL, mask)
            yield from flatten(t.elem_type, elem)
    elif isinstance(t, TMap):
        yield len(x["mapping"])
        yield from flatten(t.v, x["default"])
        for (m, k, v) in x["mapping"]:
            yield from flatten(BOOL, m)
            yield from flatten(t.k, k)
            yield from flatten(t.v, v)
    else:
        raise NotImplementedError(t)

def pack(t, it):
    # MUST agree with flatten()
    h = extension_handler(type(t))
    if h is not None:
        return pack(h.encoding_type(t), it)

    try:
        if decideable(t):
            return next(it)
        elif isinstance(t, TTuple):
            return tuple(pack(tt, it) for tt in t.ts)
        elif isinstance(t, TRecord):
            return { f : pack(tt, it) for f, tt in t.fields }
        elif isinstance(t, THandle):
            return (pack(INT, it), pack(t.value_type, it))
        elif is_collection(t):
            n = next(it)
            mask = []
            elems = []
            for i in range(n):
                mask.append(pack(BOOL, it))
                elems.append(pack(t.elem_type, it))
            return (mask, elems)
        elif isinstance(t, TMap):
            n = next(it)
            default = pack(t.v, it)
            mapping = []
            for i in range(n):
                mapping.append((
                    pack(BOOL, it),
                    pack(t.k, it),
                    pack(t.v, it)))
            return {"default": default, "mapping": mapping}
        raise NotImplementedError(t)
    except StopIteration:
        raise ValueError("not enough entries in iterable while unpacking {}".format(pprint(t)))

def to_bool(e : z3.AstRef):
    """
    If `e` is a boolean literal, return its value (True or False).
    Otherwise, return None.
    """
    if z3.is_true(e):
        return True
    if z3.is_false(e):
        return False
    return None

@typechecked
def ite(ty : Type, cond : z3.AstRef, then_branch, else_branch):
    b = to_bool(cond)
    if b is not None:
        return then_branch if b else else_branch

    h = extension_handler(type(ty))
    if h is not None:
        return ite(h.encoding_type(ty), cond, then_branch, else_branch)

    ctx = cond.ctx
    assert isinstance(ctx, z3.Context)
    if decideable(ty):
        return z3.If(cond, then_branch, else_branch, ctx)
    elif is_collection(ty):
        assert isinstance(then_branch, tuple)
        assert isinstance(else_branch, tuple)
        then_mask, then_elems = then_branch
        else_mask, else_elems = else_branch
        maxlen = max(len(then_mask), len(else_mask))
        mask = []
        elems = []
        ncond = z3.Not(cond, ctx)
        for i in range(maxlen):
            if i < len(then_mask) and i < len(else_mask):
                mask.append(z3.If(cond, then_mask[i], else_mask[i], ctx))
                elems.append(ite(ty.elem_type, cond, then_elems[i], else_elems[i]))
            elif i < len(then_mask):
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
    else:
        raise NotImplementedError(pprint(ty))

def grid(rows, cols):
    return [[None for c in range(cols)] for r in range(rows)]

class ToZ3(Visitor):
    def __init__(self, z3ctx, z3solver):
        self.ctx = z3ctx
        self.solver = z3solver
        self.int_zero = z3.IntVal(0, self.ctx)
        self.int_one  = z3.IntVal(1, self.ctx)
        self.true = z3.BoolVal(True, self.ctx)
        self.false = z3.BoolVal(False, self.ctx)
        assert to_bool(self.true) is True
        assert to_bool(self.false) is False
        assert to_bool(self.int_zero) is None

    def bool_to_z3(self, b):
        return self.true if b else self.false

    def bfold(self, xs : [z3.AstRef], f, identity : bool, bottom : bool):
        xs = make_random_access(xs)
        bs = [to_bool(c) for c in xs]
        if any(b is bottom for b in bs):
            return self.bool_to_z3(bottom)
        xs = [c for (c, b) in zip(xs, bs) if b is not identity]
        if not xs:
            return self.bool_to_z3(identity)
        return f(*xs, self.ctx)

    def all(self, *conds): return self.bfold(conds, z3.And, True, False)
    def any(self, *conds): return self.bfold(conds, z3.Or,  False, True)
    def neg(self, cond):
        b = to_bool(cond)
        if b is True:  return self.false
        if b is False: return self.true
        return z3.Not(cond, self.ctx)
    def implies(self, l, r):
        b = to_bool(l)
        if b is True:  return r
        if b is False: return self.true
        b = to_bool(r)
        if b is True:  return self.true
        if b is False: return self.neg(l)
        return z3.Implies(l, r, self.ctx)

    def distinct(self, t, *values):
        if len(values) <= 1:
            return z3.BoolVal(True, self.ctx)
        return self.all(
            self.distinct(t, values[1:]),
            *[self.neg(self.eq(t, values[0], v1, {})) for v1 in values[1:]])
    def lt(self, t, e1, e2, env, deep=False):
        if e1 is e2:
            return self.false
        if decideable(t):
            return e1 < e2
        else:
            raise NotImplementedError(t)
    def gt(self, t, e1, e2, env, deep=False):
        if e1 is e2:
            return self.false
        if decideable(t):
            return e1 > e2
        else:
            raise NotImplementedError(t)
    def eq(self, t, e1, e2, deep=False):
        if e1 is e2:
            return self.true

        h = extension_handler(type(t))
        if h is not None:
            t = h.encoding_type(t)

        if decideable(t):
            assert isinstance(e1, z3.AstRef), "{}".format(repr(e1))
            assert isinstance(e2, z3.AstRef), "{}".format(repr(e2))
            return e1 == e2
        elif isinstance(t, TList) or (is_collection(t) and deep):
            elem_type = t.elem_type
            lhs_mask, lhs_elems = e1
            rhs_mask, rhs_elems = e2

            # eqs[i][j] := lhs[i] == rhs[j]
            eqs = grid(len(lhs_mask), len(rhs_mask))
            for (row, l) in enumerate(lhs_elems):
                for (col, r) in enumerate(rhs_elems):
                    eqs[row][col] = self.eq(elem_type, l, r, deep=deep)

            # res[i][j] := lhs[i:] ?= rhs[i:]
            res = grid(len(lhs_mask) + 1, len(rhs_mask) + 1)
            # . . . v
            # . . . v
            # . . . v
            # > > > ETRUE
            res[len(lhs_mask)][len(rhs_mask)] = self.true
            for row in reversed(range(len(lhs_mask))):
                res[row][len(rhs_mask)] = self.all(
                    res[row+1][len(rhs_mask)],
                    self.neg(lhs_mask[row]))
            for col in reversed(range(len(rhs_mask))):
                res[len(lhs_mask)][col] = self.all(
                    res[len(lhs_mask)][col+1],
                    self.neg(rhs_mask[col]))

            for row in reversed(range(len(lhs_mask))):
                for col in reversed(range(len(rhs_mask))):
                    lhs_m = lhs_mask[row]
                    rhs_m = rhs_mask[col]
                    res[row][col] = (
                        ite(BOOL, lhs_m,
                            ite(BOOL, rhs_m,
                                # both masks are true
                                self.all(eqs[row][col], res[row+1][col+1]),
                                # only lhs mask: skip rhs
                                res[row][col+1]),
                            ite(BOOL, rhs_m,
                                # only rhs mask: skip lhs
                                res[row+1][col],
                                # neither: skip both
                                res[row+1][col+1])))
            return res[0][0]

        elif isinstance(t, TBag) or isinstance(t, TSet):
            elem_type = t.elem_type
            lhs_mask, lhs_elems = e1
            rhs_mask, rhs_elems = e2

            # n = max(len(lhs_elems), len(rhs_elems))

            # lengths equal... might not be necessary
            e1len = self.len_of(e1)
            e2len = self.len_of(e2)
            conds = []
            conds.append(e1len == e2len)

            lhs_counts = [ (x, self.count_in(elem_type, e1, x, deep=deep)) for x in lhs_elems ]
            for x, count in lhs_counts:
                conds.append(count == self.count_in(elem_type, e2, x, deep=deep))

            rhs_counts = [ (x, self.count_in(elem_type, e1, x, deep=deep)) for x in rhs_elems ]
            for x, count in rhs_counts:
                conds.append(count == self.count_in(elem_type, e1, x, deep=deep))

            return self.all(*conds)
        elif isinstance(t, TMap):
            conds = [self.eq(t.v, e1["default"], e2["default"], deep=deep)]
            def map_keys(m):
                return ([mask for (mask, k, v) in m["mapping"]], [k for (mask, k, v) in m["mapping"]])
            e1keys = map_keys(e1)
            e2keys = map_keys(e2)
            conds.append(self.eq(
                TBag(t.k),
                self.distinct_bag_elems(e1keys, t.k),
                self.distinct_bag_elems(e2keys, t.k),
                deep=False))
            for (mask, k, v) in e1["mapping"] + e2["mapping"]:
                conds.append(self.implies(mask, self.eq(
                    t.v,
                    self._map_get(t, e1, k),
                    self._map_get(t, e2, k),
                    deep=deep)))
            return self.all(*conds)
        elif isinstance(t, THandle):
            h1, val1 = e1
            h2, val2 = e2
            res = h1 == h2
            if deep:
                res = self.all(res, self.eq(t.value_type, val1, val2, deep=deep))
            return res
        elif isinstance(t, TRecord):
            conds = [self.eq(tt, e1[f], e2[f], deep=deep) for (f, tt) in t.fields]
            return self.all(*conds)
        elif isinstance(t, TTuple):
            conds = [self.eq(t, x, y, deep=deep) for (t, x, y) in zip(t.ts, e1, e2)]
            return self.all(*conds)
        else:
            raise NotImplementedError(t)
    def count_in(self, t, bag, x, deep=False):
        """
        t - type of elems in bag
        bag - a bag
        x - elem

        returns # of times x appears in bag
        """
        bag_mask, bag_elems = bag
        l = self.int_zero
        for i in range(len(bag_elems)):
            l = ite(INT, self.all(bag_mask[i], self.eq(t, x, bag_elems[i], deep=deep)), self.int_one, self.int_zero) + l
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
            self.all(mask, self.eq(t, x, elem, deep=deep))
            for (mask, elem) in zip(bag_mask, bag_elems)]
        return self.any(*conds)
    def len_of(self, val):
        bag_mask, bag_elems = val
        l = self.int_zero
        for i in range(len(bag_elems)):
            l = ite(INT, bag_mask[i], self.int_one, self.int_zero) + l
        return l
    def visit_TInt(self, t):
        return z3.IntSort(self.ctx)
    def visit_TLong(self, t):
        return z3.IntSort(self.ctx)
    def visit_TFloat(self, t):
        return z3.RealSort(self.ctx)
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
        elif n.type in (REAL, FLOAT):
            return z3.RealVal(n.val, self.ctx)
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
        return ([self.true], [self.visit(e.e, env)])
    def visit_EHandle(self, e, env):
        return (self.visit(e.addr, env), self.visit(e.value, env))
    def visit_ENull(self, e, env):
        return (self.false, self.mkval(e.type.elem_type))
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
        return self.visit(e.e, env)[e.index]
    def visit_EFlatMap(self, e, env):
        mask, elems = self.visit(EMap(e.e, e.key_function).with_type(TBag(e.key_function.body.type)), env)
        res_mask = []
        res_elems = []
        for m, es in zip(mask, elems):
            sub_mask, sub_elems = es
            for mm, ee in zip(sub_mask, sub_elems):
                res_mask.append(self.all(m, mm))
                res_elems.append(ee)
        return (res_mask, res_elems)
    def visit_ECond(self, e, env):
        cond = self.visit(e.cond, env)
        then_branch = self.visit(e.then_branch, env)
        else_branch = self.visit(e.else_branch, env)
        return ite(e.type, cond, then_branch, else_branch)
    def distinct_bag_elems(self, bag, elem_type):
        mask, elems = bag
        if elems:
            rest_mask, rest_elems = self.raw_filter(
                self.distinct_bag_elems((mask[1:], elems[1:]), elem_type),
                lambda x: self.implies(mask[0], self.neg(self.eq(elem_type, elems[0], x))))
            return ([mask[0]] + rest_mask, [elems[0]] + rest_elems)
        else:
            return bag
    def visit_EUnaryOp(self, e, env):
        if e.op == UOp.Not:
            return self.neg(self.visit(e.e, env))
        elif e.op == UOp.Sum:
            bag = self.visit(e.e, env)
            bag_mask, bag_elems = bag
            sum = self.int_zero
            for i in range(len(bag_elems)):
                sum = ite(INT, bag_mask[i], bag_elems[i], self.int_zero) + sum
            return sum
        elif e.op == UOp.Length:
            v = EVar("v").with_type(e.e.type.elem_type)
            return self.visit(EUnaryOp(UOp.Sum, EMap(e.e, ELambda(v, ONE)).with_type(TBag(INT))).with_type(e.type), env)
        elif e.op == UOp.AreUnique:
            def is_unique(bag):
                bag_mask, bag_elems = bag
                rest = (bag_mask[1:], bag_elems[1:])
                if bag_elems:
                    return self.all(
                        self.implies(bag_mask[0], self.neg(self.is_in(e.e.type.elem_type, rest, bag_elems[0], env))),
                        is_unique(rest))
                else:
                    return self.true
            return is_unique(self.visit(e.e, env))
        elif e.op == UOp.Empty:
            mask, elems = self.visit(e.e, env)
            return self.neg(self.any(*mask))
        elif e.op == UOp.Exists:
            mask, elems = self.visit(e.e, env)
            return self.any(*mask)
        elif e.op == UOp.All:
            mask, elems = self.visit(e.e, env)
            return self.all(*[self.implies(m, e) for (m, e) in zip(mask, elems)])
        elif e.op == UOp.Any:
            mask, elems = self.visit(e.e, env)
            return self.any(*[self.all(m, e) for (m, e) in zip(mask, elems)])
        elif e.op == UOp.Distinct:
            elem_type = e.type.elem_type
            return self.distinct_bag_elems(self.visit(e.e, env), elem_type)
        elif e.op == UOp.Length:
            return self.len_of(self.visit(e.e, env))
        elif e.op == UOp.The:
            t = e.type
            bag = self.visit(e.e, env)
            mask, elems = bag
            exists = self.any(*mask)
            elem = self.mkval(t)
            for (m, e) in reversed(list(zip(mask, elems))):
                elem = ite(t, m, e, elem)
            return elem
        elif e.op == UOp.Reversed:
            mask, elems = self.visit(e.e, env)
            return (list(reversed(mask)), list(reversed(elems)))
        elif e.op == "-":
            return -self.visit(e.e, env)
        else:
            raise NotImplementedError(e.op)
    def _optimal(self, e, env, cmp):
        keytype = e.key_function.body.type
        mask, elems = self.visit(e.e, env)

        if not elems:
            return self.mkval(e.type)

        # print(pprint(e))

        # 1st pass: find the best key
        first = True
        bestkey = None
        legal = self.false
        f = self.visit(e.key_function, env)
        keyelems = [f(x) for x in elems]
        for m, key in reversed(list(zip(mask, keyelems))):
            if first:
                bestkey = key
                first = False
                legal = m
            else:
                bestkey = ite(keytype,
                    self.any(self.all(m, cmp(keytype, key, bestkey, env)), self.neg(legal)),
                    key,
                    bestkey)
                legal = self.any(m, legal)
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
                    self.any(self.all(m, self.eq(keytype, key, bestkey)), self.neg(legal)),
                    x,
                    res)
                legal = self.any(m, legal)
        # print(" -> res={}".format(res))

        return ite(e.type, legal, res, self.mkval(e.type))
    def visit_EArgMin(self, e, env):
        return self._optimal(e, env, self.lt)
    def visit_EArgMax(self, e, env):
        return self._optimal(e, env, self.gt)
    def visit_EGetField(self, e, env):
        r = self.visit(e.e, env)
        if isinstance(e.e.type, THandle):
            assert e.field_name == "val"
            h, val = r
            return val
        else:
            return r[e.field_name]
    def remove_one(self, elem_type, bag, elem, mask):
        masks, elems = bag
        if not masks:
            return bag
        m = masks[0]
        e = elems[0]
        removed = self.all(m, mask, self.eq(elem_type, elem, e))
        m = self.all(m, self.neg(removed))
        mrest, erest = self.remove_one(elem_type, (masks[1:], elems[1:]), elem, self.all(mask, self.neg(removed)))
        return ([m] + mrest, [e] + erest)
    def remove_all(self, bag_type, bag, to_remove, env):
        elem_type = bag_type.elem_type
        for m, e in zip(*to_remove):
            bag = self.remove_one(elem_type, bag, e, m)
        return bag
    def visit_EBinOp(self, e, env):
        # optimization: x in (distinct y) --> x in y
        # ("distinct" is very expensive for the solver)
        if e.op == BOp.In and isinstance(e.e2, EUnaryOp) and e.e2.op == UOp.Distinct:
            return self.visit(EIn(e.e1, e.e2.e), env)

        # normal path
        v1 = self.visit(e.e1, env)
        v2 = self.visit(e.e2, env)
        if e.op == BOp.And:
            return self.all(v1, v2)
        elif e.op == BOp.Or:
            return self.any(v1, v2)
        elif e.op == "=>":
            return self.implies(v1, v2)
        elif e.op == "==":
            return self.eq(e.e1.type, v1, v2)
        elif e.op == "!=":
            return self.neg(self.eq(e.e1.type, v1, v2))
        elif e.op == "===":
            return self.eq(e.e1.type, v1, v2, deep=True)
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
            if isinstance(e.type, TBag) or isinstance(e.type, TList):
                return (v1[0] + v2[0], v1[1] + v2[1])
            elif isinstance(e.type, TSet):
                return self.visit(EUnaryOp(UOp.Distinct, EBinOp(e.e1, "+", e.e2).with_type(TBag(e.type.elem_type))).with_type(TBag(e.type.elem_type)), env)
            elif is_numeric(e.type):
                return v1 + v2
            else:
                raise NotImplementedError(e.type)
        elif e.op == "-":
            if isinstance(e.type, TBag) or isinstance(e.type, TSet) or isinstance(e.type, TList):
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
    def visit_EListGet(self, e, env):
        def f(l, idx):
            mask, elems = l
            if not mask:
                return self.mkval(e.type)
            m = mask[0]
            x = elems[0]
            succ = ite(INT, m, self.int_one, self.int_zero)
            return ite(e.type, self.all(m, self.eq(INT, idx, self.int_zero)),
                x,
                f((mask[1:], elems[1:]), idx - succ))
        return f(self.visit(e.e, env), self.visit(e.index, env))
    def visit_EListSlice(self, e, env):
        def symb_slice(l, st, ed, idx):
            if not l:
                return l
            m = l[0]
            next_index = idx + ite(INT, m, self.int_one, self.int_zero)
            rest = symb_slice(l[1:], st, ed, next_index)
            return [self.all(m, st <= idx, idx < ed)] + rest
        masks, elems = self.visit(e.e, env)
        start = self.visit(e.start, env)
        end = self.visit(e.end, env)
        new_masks = symb_slice(masks, start, end, self.int_zero)
        return (new_masks, elems)
    def visit_EDropFront(self, e, env):
        def drop1(mask, elems):
            if not mask:
                return ([], [])
            m = mask[0]
            x = elems[0]
            mask = mask[1:]
            elems = elems[1:]
            return ite(e.type, m, (mask, elems), drop1(mask, elems))
        return drop1(*self.visit(e.e, env))
    def visit_EMap(self, e, env):
        f = self.visit(e.key_function, env)
        bag_mask, bag_elems = self.visit(e.e, env)
        res_elems = []
        for x in bag_elems:
            res_elems.append(f(x))
        return bag_mask, res_elems
    def do_filter(self, bag, p : ELambda, env):
        return self.raw_filter(bag, self.visit(p, env))
    def raw_filter(self, bag, p):
        bag_mask, bag_elems = bag
        res_mask = []
        for mask, x in zip(bag_mask, bag_elems):
            res_mask.append(self.all(mask, p(x)))
        return res_mask, bag_elems
    def visit_EFilter(self, e, env):
        return self.do_filter(self.visit(e.e, env), e.p, env)
    def visit_EMakeRecord(self, e, env):
        return { f:self.visit(v, env) for (f, v) in e.fields }
    def visit_EMakeMap2(self, e, env):
        bag_mask, bag_elems = self.visit(e.e, env)
        keys = zip(bag_mask, bag_elems)
        proj = self.visit(e.value_function, env)
        return {
            "mapping": [(mask, key, proj(key)) for (mask, key) in keys],
            "default": self.mkval(e.type.v) }
    def visit_EMapKeys(self, e, env):
        m = self.visit(e.e, env)
        d = m["default"]
        m = m["mapping"]
        bag_mask = [mask for (mask, k, v) in m]
        bag_elems = [k for (mask, k, v) in m]
        return self.distinct_bag_elems((bag_mask, bag_elems), e.type.elem_type)
    def _map_get(self, map_type, map, key):
        res = map["default"]
        for (mask, k, v) in reversed(map["mapping"]):
            res = ite(map_type.v, self.all(mask, self.eq(map_type.k, k, key)), v, res)
        return res
    def visit_EMapGet(self, e, env):
        map = self.visit(e.map, env)
        key = self.visit(e.key, env)
        return self._map_get(e.map.type, map, key)
    def visit_EHasKey(self, e, env):
        return self.visit(EIn(e.key, EMapKeys(e.map).with_type(TSet(e.map.type.k))), env)
    def visit_ELet(self, e, env):
        env = dict(env)
        for thing in break_let(e):
            if isinstance(thing, tuple):
                v, x = thing
                env[v.id] = self.visit(x, env)
            else:
                return self.visit(thing, env)

    def visit_ELambda(self, lam : ELambda, env):

        env = dict(env)
        cache = { }
        in_type = lam.arg.type
        body_type = lam.body.type

        def compiled_lambda(arg):
            argv = list(flatten(in_type, arg))
            key = len(argv)
            funcs = cache.get(key)

            if funcs is None:
                symb_argv = [v if isinstance(v, int) else z3.Const(fresh_name(), v.sort()) for v in argv]
                assert len(symb_argv) == len(argv)
                z3_vars = [v for v in symb_argv if not isinstance(v, int)]
                symb_arg = pack(in_type, iter(symb_argv))
                with extend(env, lam.arg.id, symb_arg):
                    res = self.visit(lam.body, env)
                funcs = []
                for z3_body in flatten(body_type, res):
                    if isinstance(z3_body, int):
                        funcs.append(z3_body)
                    else:
                        funcs.append((z3_vars, z3_body))
                cache[key] = funcs

            return pack(body_type, (f if isinstance(f, int) else z3.substitute(f[1], *zip(f[0], [x for x in argv if not isinstance(x, int)])) for f in funcs))

        return compiled_lambda

    def visit_clauses(self, clauses, e, env):
        if not clauses:
            return [True], [self.visit(e, env)]
        c = clauses[0]
        if isinstance(c, CCond):
            bag_mask, bag_elems = self.visit_clauses(clauses[1:], e, env)
            res_mask = []
            for i in range(len(bag_elems)):
                incl_this = self.all(bag_mask[i], self.visit(c.e, env))
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
                res_mask += [self.all(incl_this, bit) for bit in bag2_mask]
                res_elems += bag2_elems
            return res_mask, res_elems
    def visit_EStateVar(self, e, env):
        return self.visit(e.e, env)
    def visit_Exp(self, e, *args):
        if isinstance(e, Exp):
            h = extension_handler(type(e))
            if h is not None:
                return self.visit(h.encode(e), *args)
        raise NotImplementedError("toZ3({})".format(e))
    def visit_AstRef(self, e, env):
        """AstRef is the Z3 AST node type"""
        return e
    def visit_bool(self, e, env):
        return z3.BoolVal(e, self.ctx)
    def visit(self, e, *args):
        try:
            return super().visit(e, *args)
        except KeyboardInterrupt:
            raise
        except:
            print("failed to convert {}".format(pprint(e)))
            print("  ---> {!r}".format(e))
            print("  ---> src:  {}".format(getattr(e, "_src", "?")))
            print("  ---> type: {}".format(getattr(e, "_type_src", "?")))
            raise

    def mkval(self, type):
        """
        Create an arbitrary value of the given type. Guaranteed to agree with
        cozy.evaluation.mkval(type).
        """
        return self.unreconstruct(evaluation.mkval(type), type)

    def unreconstruct(self, value, ty):
        """Converts reconstructed value back to a Z3 value"""
        ctx = self.ctx
        if ty == INT or ty == LONG:
            return z3.IntVal(value, ctx)
        elif ty == REAL or ty == FLOAT:
            return z3.RealVal(value, ctx)
        elif isinstance(ty, TBool):
            return self.true if value else self.false
        elif is_collection(ty):
            masks = [self.true] * len(value)
            values = [self.unreconstruct(v, ty.elem_type) for v in value]
            return (masks, values)
        elif isinstance(ty, TMap):
            return {
                "mapping": [(self.true, self.unreconstruct(k, ty.k), self.unreconstruct(v, ty.v)) for (k, v) in value.items()],
                "default": self.unreconstruct(value.default, ty.v) }
        elif isinstance(ty, TEnum):
            return z3.IntVal(ty.cases.index(value), ctx)
        elif isinstance(ty, TNative):
            return z3.IntVal(value[1], ctx)
        elif isinstance(ty, THandle):
            return (z3.IntVal(value[0], ctx), self.unreconstruct(value[1], ty.value_type))
        elif isinstance(ty, TTuple):
            return tuple(self.unreconstruct(v, t) for (v, t) in zip(value, ty.ts))
        elif isinstance(ty, TRecord):
            return { f:self.unreconstruct(value[f], t) for (f, t) in ty.fields }
        elif isinstance(ty, TString):
            if all(c == "a" for c in value):
                return z3.IntVal(len(value), ctx)
            raise NotImplementedError((ty, value))
        else:
            h = extension_handler(type(ty))
            if h is not None:
                return self.unreconstruct(value, h.encoding_type(ty))
            raise NotImplementedError(ty)

    def mkvar(self, collection_depth, ty, min_collection_depth=0, on_z3_var=None, on_z3_assertion=None):
        ctx = self.ctx
        solver = self.solver
        if on_z3_var is None:
            on_z3_var = lambda v: v
        if on_z3_assertion is None:
            on_z3_assertion = solver.add

        h = extension_handler(type(ty))
        if h is not None:
            return self.mkvar(collection_depth, h.encoding_type(ty), min_collection_depth, on_z3_var, on_z3_assertion)

        if ty == INT or ty == LONG or isinstance(ty, TNative):
            return on_z3_var(z3.Int(fresh_name(), ctx=ctx))
        elif ty == REAL or ty == FLOAT:
            return on_z3_var(z3.Real(fresh_name(), ctx=ctx))
        elif ty == STRING:
            i = on_z3_var(z3.Int(fresh_name(), ctx=ctx))
            on_z3_assertion(i >= 0)
            return i
        elif ty == BOOL:
            return on_z3_var(z3.Bool(fresh_name(), ctx=ctx))
        elif isinstance(ty, TEnum):
            ncases = len(ty.cases)
            n = on_z3_var(z3.Int(fresh_name(), ctx=ctx))
            on_z3_assertion(n >= 0)
            on_z3_assertion(n < ncases)
            return n
        elif isinstance(ty, TSet):
            res = self.mkvar(collection_depth, TBag(ty.elem_type), min_collection_depth, on_z3_var, on_z3_assertion)
            mask, elems = res
            for i in range(1, len(mask)):
                on_z3_assertion(self.implies(mask[i], self.distinct(ty.elem_type, *(elems[:(i+1)]))))
            return res
        elif isinstance(ty, TBag) or isinstance(ty, TList):
            size = max(collection_depth, min_collection_depth)
            true_masks = [self.true for i in range(min_collection_depth)]
            symb_masks = [self.mkvar(collection_depth, BOOL, min_collection_depth, on_z3_var, on_z3_assertion) for i in range(size - min_collection_depth)]
            mask  = symb_masks + true_masks
            elems = [self.mkvar(collection_depth, ty.elem_type, min_collection_depth, on_z3_var, on_z3_assertion) for i in range(collection_depth)]
            # symmetry breaking
            for i in range(len(mask) - 1):
                on_z3_assertion(self.implies(mask[i], mask[i+1]))
            return (mask, elems)
        elif isinstance(ty, TMap):
            default = self.mkval(ty.v)
            mask = [self.mkvar(collection_depth, BOOL, min_collection_depth, on_z3_var, on_z3_assertion) for i in range(collection_depth)]
            # symmetry breaking
            for i in range(len(mask) - 1):
                on_z3_assertion(self.implies(mask[i], mask[i+1]))
            return {
                "mapping": [(
                    mask[i],
                    self.mkvar(collection_depth, ty.k, min_collection_depth, on_z3_var, on_z3_assertion),
                    self.mkvar(collection_depth, ty.v, min_collection_depth, on_z3_var, on_z3_assertion))
                    for i in range(collection_depth)],
                "default":
                    default }
        elif isinstance(ty, TRecord):
            return { field : self.mkvar(collection_depth, t, min_collection_depth, on_z3_var, on_z3_assertion) for (field, t) in ty.fields }
        elif isinstance(ty, TTuple):
            return tuple(self.mkvar(collection_depth, t, min_collection_depth, on_z3_var, on_z3_assertion) for t in ty.ts)
        elif isinstance(ty, THandle):
            h = on_z3_var(z3.Int(fresh_name(), ctx=ctx))
            v = (h, self.mkvar(collection_depth, ty.value_type, min_collection_depth, on_z3_var, on_z3_assertion))
            return v
        elif isinstance(ty, TFunc):
            return z3.Function(fresh_name(),
                *[self.visit(t) for t in ty.arg_types],
                self.visit(ty.ret_type))
        else:
            raise NotImplementedError(ty)

DECIDABLE_TYPES = set([TInt, TLong, TBool, TString, TEnum, TNative, TReal, TFloat])
def decideable(t : Type):
    return type(t) in DECIDABLE_TYPES

_start = None
_debug_duration = timedelta(seconds=5)
def _tick():
    global _start
    _start = datetime.now()

def _tock(e, event):
    global _start
    now = datetime.now()
    elapsed = now - _start
    _start = now
    if elapsed > _debug_duration:
        print("WARNING: took {elapsed}s to {event}".format(event=event, elapsed=elapsed.total_seconds()))

_LOCK = threading.RLock()

class ExtractedFunc(object):
    def __init__(self, cases, default):
        self.cases = cases
        self.default = default
    def __repr__(self):
        return "ExtractedFunc(cases={!r}, default={!r})".format(self.cases, self.default)
    def __str__(self):
        return repr(self)
    def __call__(self, *args):
        return self.cases.get(args, self.default)

class IncrementalSolver(object):
    SAVE_PROPS = [
        "vars",
        "funcs",
        "_env"]

    def __init__(self,
            vars = None,
            funcs = None,
            collection_depth : int = None,
            min_collection_depth : int = 0,
            validate_model : bool = True,
            model_callback = None,
            logic : str = None,
            timeout : float = None,
            do_cse : bool = True):

        if collection_depth is None:
            collection_depth = collection_depth_opt.value

        self.vars = OrderedSet()
        self.funcs = OrderedDict()
        self.min_collection_depth = min_collection_depth
        self.collection_depth = collection_depth
        self.validate_model = validate_model
        self.model_callback = model_callback
        self._env = OrderedDict()
        self.stk = []
        self.do_cse = do_cse

        with _LOCK:
            ctx = z3.Context()
            solver = z3.Solver(ctx=ctx) if logic is None else z3.SolverFor(logic, ctx=ctx)
            if use_quantified_encoding.value:
                solver.set(":smt.macro_finder", True)
            if timeout is not None:
                solver.set("timeout", int(timeout * 1000))
            solver.set("core.validate", validate_model)
            visitor = ToZ3(ctx, solver)

            self.visitor = visitor
            self.z3_solver = solver
            self._create_vars(vars=vars or (), funcs=funcs or {})

    def push(self):
        self.stk.append(tuple(type(getattr(self, p))(getattr(self, p)) for p in IncrementalSolver.SAVE_PROPS))
        self.z3_solver.push()

    def pop(self):
        x = self.stk.pop()
        for v, p in zip(x, IncrementalSolver.SAVE_PROPS):
            setattr(self, p, v)
        self.z3_solver.pop()

    def _create_vars(self, vars, funcs):
        for f, t in funcs.items():
            if f not in self._env:
                self._env[f] = self.visitor.mkvar(self.collection_depth, t, min_collection_depth=self.min_collection_depth)
                self.funcs[f] = t
        for v in vars:
            if v.id not in self._env:
                self._env[v.id] = self.visitor.mkvar(self.collection_depth, v.type, min_collection_depth=self.min_collection_depth)
                self.vars.add(v)

    def _convert(self, e):
        _tick()
        orig_e = e
        try:
            e = purify(e)
            if self.do_cse:
                orig_size = e.size()
                e = cse(e, verify=False)
                _tock(e, "cse (size: {} --> {})".format(orig_size, e.size()))
            with _LOCK:
                self._create_vars(vars=free_vars(orig_e), funcs=free_funcs(orig_e))
                with task("encode formula", size=e.size()):
                    return self.visitor.visit(e, self._env)
        except:
            print("conversion failed for: {!r}".format(orig_e))
            raise

    def add_assumption(self, e):
        try:
            with _LOCK:
                self.z3_solver.add(self._convert(e))
        except Exception:
            print(" ---> to reproduce: satisfy({e!r}, vars={vars!r}, collection_depth={collection_depth!r}, validate_model={validate_model!r})".format(
                e=e,
                vars=self.vars,
                collection_depth=self.collection_depth,
                validate_model=self.validate_model))
            raise

    def satisfy(self, e, model_extraction=True):
        _env = self._env
        solver = self.z3_solver
        vars = self.vars
        visitor = self.visitor

        if self.validate_model:
            model_extraction = True

        with _LOCK:
            _tick()

            builtin_type = type
            def reconstruct(model, value, type):
                if type == INT or type == LONG:
                    return model.eval(value, model_completion=True).as_long()
                elif type == REAL or type == FLOAT:
                    return model.eval(value, model_completion=True).as_fraction()
                elif isinstance(type, TNative):
                    return (type.name, model.eval(value, model_completion=True).as_long())
                elif type == STRING:
                    i = model.eval(value, model_completion=True).as_long()
                    return "a" * i
                elif type == BOOL:
                    return bool(model.eval(value, model_completion=True))
                elif isinstance(type, TBag) or isinstance(type, TSet) or isinstance(type, TList):
                    mask, elems = value
                    real_val = []
                    for i in range(len(elems)):
                        if reconstruct(model, mask[i], BOOL):
                            real_val.append(reconstruct(model, elems[i], type.elem_type))
                    if isinstance(type, TList):
                        return tuple(real_val)
                    return Bag(real_val)
                elif isinstance(type, TMap):
                    default = reconstruct(model, value["default"], type.v)
                    res = Map(type, default)
                    for (mask, k, v) in value["mapping"]:
                        # K/V pairs appearing earlier in value["mapping"] have precedence
                        if reconstruct(model, mask, BOOL):
                            k = reconstruct(model, k, type.k)
                            if k not in res.keys():
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
                    return Handle(id, val)
                elif isinstance(type, TRecord):
                    res = defaultdict(lambda: None)
                    for (field, t) in type.fields:
                        res[field] = reconstruct(model, value[field], t)
                    return FrozenDict(res)
                elif isinstance(type, TTuple):
                    return tuple(reconstruct(model, v, t) for (v, t) in zip(value, type.ts))
                else:
                    h = extension_handler(builtin_type(type))
                    if h is not None:
                        return reconstruct(model, value, h.encoding_type(type))
                    raise NotImplementedError(type)

            a = self._convert(e)
            solver.push()
            solver.add(a)

            _tock(e, "encode")
            with task("invoke Z3"):
                res = solver.check()
            _tock(e, "solve")
            if res == z3.unsat:
                solver.pop()
                return None
            elif res == z3.unknown:
                solver.pop()
                raise SolverReportedUnknown("z3 reported unknown")
            else:
                res = { }
                if model_extraction:
                    def mkfunc(f, arg_types, out_type):
                        z3_func = model[f]
                        if not arg_types:
                            default = reconstruct(model, f(), out_type)
                            return ExtractedFunc({}, default)
                        if z3_func is None:
                            return ExtractedFunc({}, evaluation.mkval(out_type))
                        *z3_entries, z3_default = z3_func.as_list()
                        default = reconstruct(model, z3_default, out_type)
                        entries = OrderedDict()
                        for *z3_input, z3_output in z3_entries:
                            input = tuple(reconstruct(model, i, t) for (i, t) in zip(z3_input, arg_types))
                            output = reconstruct(model, z3_output, out_type)
                            entries[input] = output
                        return ExtractedFunc(entries, default)
                    model = solver.model()
                    for name, t in self.funcs.items():
                        f = _env[name]
                        out_type = t.ret_type
                        arg_types = t.arg_types
                        res[name] = mkfunc(f, arg_types, out_type)
                    for v in vars:
                        res[v.id] = reconstruct(model, _env[v.id], v.type)
                    if self.model_callback is not None:
                        self.model_callback(res)
                    if self.validate_model:
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
                                collection_depth=repr(self.collection_depth),
                                validate_model=repr(self.validate_model)))
                            wq = [(e, _env, res)]
                            while wq:
                                x, solver_env, eval_env = wq.pop()
                                for x in sorted(all_exps(x), key=lambda xx: xx.size()):
                                    if all(v.id in eval_env for v in free_vars(x)) and not isinstance(x, ELambda):
                                        solver_val = reconstruct(model, visitor.visit(x, solver_env), x.type)
                                        v = fresh_name("tmp")
                                        eval_env[v] = solver_val
                                        eval_val = evaluation.eval(EEq(x, EVar(v).with_type(x.type)), eval_env)
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
                                                        senv = dict(solver_env)
                                                        eenv = dict(eval_env)
                                                        senv[x.p.arg.id] = elem
                                                        eenv[x.p.arg.id] = reconstruct(model, elem, x.type.elem_type)
                                                        wq.append((x.p.body, senv, eenv))
                                            elif isinstance(x, ELet):
                                                z = visitor.visit(x.e, solver_env)
                                                senv = dict(solver_env)
                                                eenv = dict(eval_env)
                                                senv[x.body_function.arg.id] = z
                                                eenv[x.body_function.arg.id] = reconstruct(model, z, x.e.type)
                                                wq.append((x.body_function.body, senv, eenv))
                                            break
                            raise ModelValidationError("model validation failed")
                    _tock(e, "extract model")
                solver.pop()
                return res

    def satisfiable(self, e):
        return self.satisfy(e, model_extraction=False) is not None

    def valid(self, e):
        return not self.satisfiable(ENot(e))

def satisfy(e, **opts):
    s = IncrementalSolver(**opts)
    return s.satisfy(e)

def satisfiable(e, **opts):
    s = IncrementalSolver(**opts)
    return s.satisfiable(e)

def valid(e, **opts):
    s = IncrementalSolver(**opts)
    return s.valid(e)

class ModelCachingSolver(object):
    """
    A non-incremental solver that caches the models it obtains.  This is useful
    if you expect to be issuing many solver queries in similar contexts; solver
    calls can often be avoided using a counterexample found on a previous call.
    """

    def __init__(self, vars : [EVar], funcs : { str : TFunc }, examples : [dict] = (), assumptions : Exp = ETRUE):
        self.vars = list(vars)
        self.funcs = OrderedDict(funcs)
        self.calls = 0
        self.hits = 0
        self.examples = list(examples)
        self.solver = IncrementalSolver(vars=vars, funcs=funcs)
        self.solver.add_assumption(assumptions)

    def satisfy(self, e):
        self.calls += 1
        eval_results = eval_bulk(e, self.examples, use_default_values_for_undefined_vars=True)
        for x, res in zip(self.examples, eval_results):
            if res:
                self.hits += 1
                return x
        x = self.solver.satisfy(e)
        if x is not None:
            self.examples.append(x)
        return x

    def satisfiable(self, e):
        return self.satisfy(e) is not None

    def valid(self, e):
        return not self.satisfiable(ENot(e))

@lru_cache()
def solver_for_context(context : Context, assumptions : Exp = ETRUE):
    return ModelCachingSolver(
        vars        = [v for v, _ in context.vars()],
        funcs       = context.funcs(),
        assumptions = assumptions)
