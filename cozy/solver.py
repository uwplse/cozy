from collections import defaultdict
from datetime import datetime
import itertools
import threading

import z3

from cozy.target_syntax import *
from cozy.syntax_tools import pprint, free_vars
from cozy.common import declare_case, fresh_name, Visitor, FrozenDict, typechecked, memoize
from cozy import evaluation

class _SymbolicUnion(object):
    """
    Represents `If(cond, x, y)` expression
    """
    def __init__(self, cond, x, y):
        self.cond = cond
        self.lhs = x
        self.rhs = y
    def map(self, f, result_ty):
        new_lhs = fmap(self.lhs, result_ty, f)
        new_rhs = fmap(self.rhs, result_ty, f)
        return SymbolicUnion(result_ty, self.cond, new_lhs, new_rhs)
    def __repr__(self):
        return "SymbolicUnion({}, {}, {})".format(repr(self.cond), repr(self.lhs), repr(self.rhs))

@typechecked
def SymbolicUnion(ty : Type, cond : z3.AstRef, then_branch, else_branch):
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
                elems.append(SymbolicUnion(ty.t, cond, then_elems[i], else_elems[i]))
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
    else:
        return _SymbolicUnion(cond, then_branch, else_branch)

def fmap(x, result_ty, f):
    if isinstance(x, _SymbolicUnion):
        return x.map(f, result_ty)
    return f(x)

class ToZ3(Visitor):
    def __init__(self, z3ctx, z3solver):
        self.ctx = z3ctx
        self.solver = z3solver
        self.funcs = { }
        self.int_zero = z3.IntVal(0, self.ctx)
        self.int_one  = z3.IntVal(1, self.ctx)
        self.handle_vars = []
    def distinct(self, t, *values):
        if len(values) <= 1:
            return z3.BoolVal(True, self.ctx)
        if decideable(t):
            return z3.Distinct(*values, self.ctx)
        return z3.And(
            self.distinct(t, values[1:]),
            *[z3.Not(self.eq(t, values[0], v1, {}), self.ctx) for v1 in values[1:]],
            self.ctx)
    def eq(self, t, e1, e2, env):
        return fmap(e1, BOOL, lambda v1:
               fmap(e2, BOOL, lambda v2:
               self._eq(t, v1, v2, env)))
    def _eq(self, t, e1, e2, env):
        if type(t) in [TInt, TLong, TBool, TEnum, TNative, TString]:
            return e1 == e2
        elif isinstance(t, TMaybe):
            if (e1 is None) and (e2 is None):
                return z3.BoolVal(True, self.ctx)
            if (e1 is None) != (e2 is None):
                return z3.BoolVal(False, self.ctx)
            return self.eq(t.t, e1, e2, env)
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

            lhs_counts = [ (x, self.count_in(elem_type, e1, x, env)) for x in lhs_elems ]
            for x, count in lhs_counts:
                conds.append(count == self.count_in(elem_type, e2, x, env))

            rhs_counts = [ (x, self.count_in(elem_type, e1, x, env)) for x in rhs_elems ]
            for x, count in rhs_counts:
                conds.append(count == self.count_in(elem_type, e1, x, env))

            return z3.And(*conds, self.ctx)
        elif isinstance(t, TMap):
            conds = [self.eq(t.v, e1["default"], e2["default"], env)]
            for (k, v) in e1["mapping"]:
                conds.append(self.eq(t.v, self._map_get(t, e1, k, env), self._map_get(t, e2, k, env), env))
            for (k, v) in e2["mapping"]:
                conds.append(self.eq(t.v, self._map_get(t, e1, k, env), self._map_get(t, e2, k, env), env))
            return z3.And(*conds, self.ctx)
        elif isinstance(t, THandle):
            h1, val1 = e1
            h2, val2 = e2
            return h1 == h2
        elif isinstance(t, TRecord):
            conds = [self.eq(tt, e1[f], e2[f], env) for (f, tt) in t.fields]
            return z3.And(*conds, self.ctx)
        elif isinstance(t, TTuple):
            conds = [self.eq(t, x, y, env) for (t, x, y) in zip(t.ts, e1, e2)]
            return z3.And(*conds, self.ctx)
        else:
            raise NotImplementedError(t)
    def count_in(self, t, bag, x, env):
        """
        t - type of elems in bag
        bag - concrete (non-SymbolicUnion) bag
        x - elem
        env - environment

        returns # of times x appears in bag
        """
        bag_mask, bag_elems = bag
        l = self.int_zero
        for i in range(len(bag_elems)):
            l = z3.If(z3.And(bag_mask[i], self.eq(t, x, bag_elems[i], env), self.ctx), self.int_one, self.int_zero, ctx=self.ctx) + l
        return l
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
        if n.type == TInt():
            return z3.IntVal(n.val, self.ctx)
        raise NotImplementedError(n.type)
    def visit_EBool(self, b, env):
        return z3.BoolVal(b.val, self.ctx)
    def visit_EEmptyList(self, e, env):
        return ([], [])
    def visit_ESingleton(self, e, env):
        return ([z3.BoolVal(True, self.ctx)], [self.visit(e.e, env)])
    def visit_EJust(self, e, env):
        return self.visit(e.e, env)
    def flatten(self, e, env):
        if decideable(e.type):
            yield (self.visit(e, env), e.type)
        else:
            raise NotImplementedError(e.type)
    def visit_ECall(self, call, env):
        args = [x for arg in call.args for x in self.flatten(arg, env)]
        key = (call.func, call.type, tuple(t for (v, t) in args))
        f = self.funcs.get(key)
        if f is None:
            f = z3.Function(fresh_name(call.func), *[self.visit(t) for (v, t) in args], self.visit(call.type))
            self.funcs[key] = f
        return f(*[v for (v, t) in args])
    def visit_EEnumEntry(self, e, env):
        return e.type.cases.index(e.name)
    def visit_ETuple(self, e, env):
        return tuple(self.visit(ee, env) for ee in e.es)
    def visit_ETupleGet(self, e, env):
        tup = self.visit(e.e, env)
        return fmap(tup, e.type, lambda tup: tup[e.n])
    def visit_EAlterMaybe(self, e, env):
        return fmap(self.visit(e.e, env), e.type,
            lambda res: self.apply(e.f, res, env) if res is not None else res)
    def visit_EFlatten(self, e, env):
        def go(bag):
            mask, elems = bag
            if not mask:
                return bag
            def recurse(sub_bag):
                exists = mask[0]
                sub_mask, sub_elems = sub_bag
                return fmap(go((mask[1:], elems[1:])), e.type,
                    lambda rest: ([z3.And(exists, m, self.ctx) for m in sub_mask] + rest[0], sub_elems + rest[1]))
            return fmap(elems[0], e.type, recurse)
        flat = fmap(self.visit(e.e, env), e.type, go)
        # print("bag = {}".format(self.visit(e.e, env)))
        # print("flat = {}".format(flat))
        return flat
    def visit_EFlatMap(self, e, env):
        return self.visit(EFlatten(EMap(e.e, e.f).with_type(TBag(e.f.body.type))).with_type(e.type), env)
    def visit_ECond(self, e, env):
        cond = self.visit(e.cond, env)
        then_branch = self.visit(e.then_branch, env)
        else_branch = self.visit(e.else_branch, env)
        return SymbolicUnion(e.type, cond, then_branch, else_branch)
    def visit_EUnaryOp(self, e, env):
        if e.op == "not":
            return z3.Not(self.visit(e.e, env), ctx=self.ctx)
        elif e.op == "sum":
            def take_sum(bag):
                bag_mask, bag_elems = bag
                sum = self.int_zero
                for i in range(len(bag_elems)):
                    sum = z3.If(bag_mask[i], bag_elems[i], self.int_zero, ctx=self.ctx) + sum
                return sum
            return fmap(self.visit(e.e, env), e.type, take_sum)
        elif e.op == "unique":
            def is_unique(bag):
                bag_mask, bag_elems = bag
                rest = (bag_mask[1:], bag_elems[1:])
                if bag_elems:
                    return z3.And(
                        z3.Implies(bag_mask[0], self.count_in(e.e.type.t, rest, bag_elems[0], env) ==  self.int_zero, self.ctx),
                        is_unique(rest),
                        self.ctx)
                else:
                    return z3.BoolVal(True, self.ctx)
            return fmap(self.visit(e.e, env), e.type, is_unique)
        elif e.op == "len":
            return fmap(self.visit(e.e, env), e.type, self.len_of)
        elif e.op == "the":
            assert isinstance(e.type, TMaybe)
            def get_first(bag):
                bag_mask, bag_elems = bag
                if not bag_elems:
                    return None
                rest = (bag_mask[1:], bag_elems[1:])
                return SymbolicUnion(e.type, bag_mask[0], bag_elems[0], get_first(rest))
            return fmap(self.visit(e.e, env), e.type, get_first)
        elif e.op == "-":
            return -self.visit(e.e, env)
        else:
            raise NotImplementedError(e.op)
    def visit_EWithAlteredValue(self, e, env):
        def go(handle, new_value):
            id, val = handle
            return (id, new_value)
        return fmap(self.visit(e.handle, env), e.type, lambda h:
               fmap(self.visit(e.new_value, env), e.type.value_type, lambda v: go(h, v)))
    def visit_EGetField(self, e, env):
        def go(r):
            if isinstance(e.e.type, THandle):
                assert e.f == "val"
                h, val = r
                return val
            else:
                return r[e.f]
        return fmap(self.visit(e.e, env), e.type, go)
    def visit_EBinOp(self, e, env):
        v1 = self.visit(e.e1, env)
        v2 = self.visit(e.e2, env)
        if e.op == "and":
            return z3.And(v1, v2, self.ctx)
        elif e.op == "or":
            return z3.Or(v1, v2, self.ctx)
        elif e.op == "==":
            return self.eq(e.e1.type, v1, v2, env)
        elif e.op == ">":
            return v1 > v2
        elif e.op == "<":
            return v1 < v2
        elif e.op == ">=":
            return v1 >= v2
        elif e.op == "<=":
            return v1 <= v2
        elif e.op == "+":
            if isinstance(e.type, TBag):
                return fmap(v1, e.type, lambda bag1:
                       fmap(v2, e.type, lambda bag2:
                       (bag1[0] + bag2[0], bag1[1] + bag2[1])))
            elif isinstance(e.type, TInt):
                return v1 + v2
            else:
                raise NotImplementedError(e.type)
        elif e.op == "-":
            return v1 - v2
        elif e.op == "in":
            return fmap(v2, e.type, lambda bag: self.count_in(e.e1.type, bag, v1, env) > self.int_zero)
        else:
            raise NotImplementedError(e.op)
    def visit_EListComprehension(self, e, env):
        x = self.visit_clauses(e.clauses, e.e, env)
        # print("{} ==> {}".format(pprint(e), x))
        return self.visit_clauses(e.clauses, e.e, env)
    def visit_EMap(self, e, env):
        def go(bag):
            bag_mask, bag_elems = bag
            res_elems = []
            for x in bag_elems:
                res_elems.append(self.apply(e.f, x, env))
            return bag_mask, res_elems
        return fmap(self.visit(e.e, env), e.type, go)
    def do_filter(self, bag, p, env):
        return self.raw_filter(bag, lambda x: self.apply(p, x, env))
    def raw_filter(self, bag, p):
        bag_mask, bag_elems = bag
        res_mask = []
        for mask, x in zip(bag_mask, bag_elems):
            res_mask.append(z3.And(mask, p(x), self.ctx))
        return res_mask, bag_elems
    def visit_EFilter(self, e, env):
        return fmap(self.visit(e.e, env), e.type, lambda bag: self.do_filter(bag, e.p, env))
    def visit_EMakeMap(self, e, env):
        def go(bag):
            bag_mask, bag_elems = bag
            ks = [ self.apply(e.key, x, env) for x in bag_elems ]
            x = EVar(fresh_name()).with_type(e.e.type.t)
            m = {"mapping": [(k, self.apply(
                    e.value,
                    self.raw_filter(bag, lambda x: self.eq(e.key.body.type, self.apply(e.key, x, env), k, env)),
                    env)) for k in ks],
                "default": self.apply(e.value, ([], []), env)}
            return m
        return fmap(self.visit(e.e, env), e.type, go)
    def visit_EMakeRecord(self, e, env):
        return { f:self.visit(v, env) for (f, v) in e.fields }
    def _map_get(self, map_type, map, key, env):
        res = map["default"]
        # print("map get {} on {}".format(key, map))
        for (k, v) in map["mapping"]:
            # print("   k   = {}".format(repr(k)))
            # print("   key = {}".format(repr(key)))
            # print("   v   = {}".format(repr(v)))
            # print("   res = {}".format(repr(res)))
            res = SymbolicUnion(map_type.v, self.eq(map_type.k, k, key, env), v, res)
        return res
    def visit_EMapGet(self, e, env):
        key = self.visit(e.key, env)
        def go(map):
            return self._map_get(e.map.type, map, key, env)
        return fmap(self.visit(e.map, env), e.type, go)
    def visit_EApp(self, e, env):
        return self.apply(e.f, self.visit(e.arg, env), env)
    def apply(self, lam, arg, env):
        env2 = dict(env)
        env2[lam.arg.id] = arg
        return self.visit(lam.body, env2)
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

    def mkvar(self, ctx, solver, collection_depth, type):
        if type == TInt() or type == TLong() or isinstance(type, TNative) or type == TString():
            return z3.Int(fresh_name(), ctx=ctx)
        elif type == TBool():
            return z3.Bool(fresh_name(), ctx=ctx)
        elif isinstance(type, TEnum):
            ncases = len(type.cases)
            n = z3.Int(fresh_name(), ctx=ctx)
            solver.add(n >= 0)
            solver.add(n < ncases)
            return n
        elif isinstance(type, TSet):
            res = self.mkvar(ctx, solver, collection_depth, TBag(type.t))
            mask, elems = res
            for i in range(1, len(mask)):
                solver.add(z3.Implies(mask[i], self.distinct(type.t, *(elems[:(i+1)])), ctx))
            return res
        elif isinstance(type, TBag):
            mask = [self.mkvar(ctx, solver, collection_depth, TBool()) for i in range(collection_depth)]
            elems = [self.mkvar(ctx, solver, collection_depth, type.t) for i in range(collection_depth)]
            # symmetry breaking
            for i in range(len(mask) - 1):
                solver.add(z3.Implies(mask[i], mask[i+1], ctx))
            return (mask, elems)
        elif isinstance(type, TMap):
            default = self.mkvar(ctx, solver, collection_depth, type.v)
            return {
                "mapping": [(
                    self.mkvar(ctx, solver, collection_depth, type.k),
                    self.mkvar(ctx, solver, collection_depth, type.v))
                    for i in range(collection_depth)],
                "default":
                    default }
        elif isinstance(type, TRecord):
            # TODO: use Z3 ADTs
            return { field : self.mkvar(ctx, solver, collection_depth, t) for (field, t) in type.fields }
        elif isinstance(type, TTuple):
            # TODO: use Z3 ADTs
            return tuple(self.mkvar(ctx, solver, collection_depth, t) for t in type.ts)
        elif isinstance(type, THandle):
            h = z3.Int(fresh_name(), ctx)
            v = (h, self.mkvar(ctx, solver, collection_depth, type.value_type))
            self.handle_vars.append((type.value_type,) + v)
            return v
        else:
            raise NotImplementedError(type)

def decideable(t):
    return type(t) in [TInt, TLong, TBool, TString, TEnum, TNative]

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
def satisfy(e, vars = None, collection_depth : int = 2, validate_model : bool = True):
    start = datetime.now()
    with _LOCK:
        # print("Checking sat (|e|={}); time to acquire lock = {}".format(e.size(), datetime.now() - start))
        start = datetime.now()
        # print("sat? {}".format(pprint(e)))
        assert e.type == TBool()

        ctx = z3.Context()
        solver = z3.Solver(ctx=ctx)
        solver.set("core.validate", validate_model)
        visitor = ToZ3(ctx, solver)

        def reconstruct(model, value, type):
            if type == TInt() or type == TLong():
                return model.eval(value, model_completion=True).as_long()
            elif isinstance(type, TNative):
                return (type.name, model.eval(value, model_completion=True).as_long())
            elif type == TString():
                i = model.eval(value, model_completion=True).as_long()
                s = "b"
                if i >= 0:
                    s += "b" * i
                else:
                    s = "a" * (-i) + s
                return s
            elif type == TBool():
                return bool(model.eval(value, model_completion=True))
            elif isinstance(type, TBag) or isinstance(type, TSet):
                mask, elems = value
                real_val = []
                for i in range(len(elems)):
                    if reconstruct(model, mask[i], TBool()):
                        real_val.append(reconstruct(model, elems[i], type.t))
                return evaluation.Bag(real_val)
            elif isinstance(type, TMap):
                default = reconstruct(model, value["default"], type.v)
                res = evaluation.hashable_defaultdict(lambda: default)
                for (k, v) in value["mapping"]:
                    # K/V pairs appearing later in value["mapping"] have precedence,
                    # so overwriting here is the correct move.
                    k = reconstruct(model, k, type.k)
                    v = reconstruct(model, v, type.v)
                    if v == default:
                        if k in res:
                            del res[k]
                    else:
                        res[k] = v
                return res
            elif isinstance(type, TEnum):
                val = model.eval(value, model_completion=True).as_long()
                return type.cases[val]
            elif isinstance(type, THandle):
                id, val = value
                id = reconstruct(model, id, TInt())
                val = reconstruct(model, val, type.value_type)
                return (id, val)
            elif isinstance(type, TRecord):
                res = defaultdict(lambda: None)
                for (field, t) in type.fields:
                    res[field] = reconstruct(model, value[field], t)
                return FrozenDict(res)
            elif isinstance(type, TTuple):
                return tuple(reconstruct(model, v, t) for (v, t) in zip(value, type.ts))
            else:
                raise NotImplementedError(type)

        def unreconstruct(value, type):
            """Converts reconstructed value back to a Z3 value"""
            if type == TInt() or type == TLong():
                return z3.IntVal(value, ctx)
            elif isinstance(type, TNative):
                return z3.IntVal(value[1], ctx)
            else:
                raise NotImplementedError(type)

        _env = { }
        fvs = vars if vars is not None else free_vars(e)
        for v in fvs:
            # print("{} : {}".format(pprint(v), pprint(v.type)))
            _env[v.id] = visitor.mkvar(ctx, solver, collection_depth, v.type)
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
            raise Exception("z3 reported unknown")
        else:
            model = solver.model()
            # print(model)
            res = { }
            for v in fvs:
                res[v.id] = reconstruct(model, _env[v.id], v.type)
            for k, f in visitor.funcs.items():
                name = k[0]
                out_type = k[1]
                arg_types = k[2]
                @memoize
                def extracted_func(*args):
                    return reconstruct(model, f(*[unreconstruct(v, t) for (v, t) in zip(args, arg_types)]), out_type)
                res[name] = extracted_func
            # print(res)
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
                    raise Exception("model validation failed")
            return res

def satisfiable(e, **opts):
    return satisfy(e, **opts) is not None

def valid(e, **opts):
    return satisfy(EUnaryOp("not", e).with_type(TBool()), **opts) is None
