from collections import defaultdict
import itertools

import z3

from syntax import *
from syntax_tools import pprint, free_vars
from common import declare_case, fresh_name, Visitor, FrozenDict

# TODO: Int==Bv32, Long==Bv64
TBitVec = declare_case(Type, "TBitVec", ["width"])

class ToZ3(Visitor):
    def __init__(self, z3ctx):
        self.ctx = z3ctx
    def eq(self, t, e1, e2, env):
        if type(t) in [TInt, TLong, TBool, TEnum]:
            return e1 == e2
        elif isinstance(t, TBag):
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
        elif isinstance(t, THandle):
            h1, val1 = e1
            h2, val2 = e2
            return h1 == h2
        else:
            raise NotImplementedError(t)
    def count_in(self, t, bag, x, env):
        bag_mask, bag_elems = bag
        l = 0
        for i in range(len(bag_elems)):
            l = z3.If(z3.And(bag_mask[i], self.eq(t, x, bag_elems[i], env), self.ctx), 1, 0, ctx=self.ctx) + l
        return l
    def len_of(self, val):
        bag_mask, bag_elems = val
        l = 0
        for i in range(len(bag_elems)):
            l = z3.If(bag_mask[i], 1, 0, ctx=self.ctx) + l
        return l
    def visit_EVar(self, v, env):
        return env[v.id]
    def visit_ENum(self, n, env):
        return n.val
    def visit_EBool(self, b, env):
        return b.val
    def visit_EEnumEntry(self, e, env):
        return e.type.cases.index(e.name)
    def visit_EUnaryOp(self, e, env):
        if e.op == "not":
            return z3.Not(self.visit(e.e, env), ctx=self.ctx)
        elif e.op == "sum":
            bag_mask, bag_elems = self.visit(e.e, env)
            sum = 0
            for i in range(len(bag_elems)):
                sum = z3.If(bag_mask[i], bag_elems[i], 0, ctx=self.ctx) + sum
            return sum
        elif e.op == "len":
            return self.len_of(self.visit(e.e, env))
        else:
            raise NotImplementedError(e.op)
    def visit_EGetField(self, e, env):
        r = self.visit(e.e, env)
        if isinstance(e.e.type, THandle):
            assert e.f == "val"
            h, val = r
            return val
        else:
            return r[e.f]
    def visit_EBinOp(self, e, env):
        if e.op == "and":
            return z3.And(self.visit(e.e1, env), self.visit(e.e2, env), self.ctx)
        elif e.op == "or":
            return z3.Or(self.visit(e.e1, env), self.visit(e.e2, env), self.ctx)
        elif e.op == "==":
            return self.eq(e.e1.type, self.visit(e.e1, env), self.visit(e.e2, env), env)
        elif e.op == "+":
            return self.visit(e.e1, env) + self.visit(e.e2, env)
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
    def visit_EFilter(self, e, env):
        bag_mask, bag_elems = self.visit(e.e, env)
        res_mask = []
        for mask, x in zip(bag_mask, bag_elems):
            res_mask.append(z3.And(mask, self.apply(e.p, x, env), self.ctx))
        return res_mask, bag_elems
    def visit_EMakeMap(self, e, env):
        # TODO: visiting e.e twice here is bad
        bag_mask, bag_elems = self.visit(e.e, env)
        ks = [ self.apply(e.key, x, env) for x in bag_elems ]
        x = EVar(fresh_name()).with_type(e.e.type.t)
        m = {"mapping": [(k, self.apply(
            e.value,
            self.visit(
                EListComprehension(x,
                    (CPull(x.id, e.e),
                     CCond(EBinOp(e.key.apply_to(x), "==", k)))),
                env),
            env)) for k in ks],
            "default": e.value}
        return m
    def visit_EMapGet(self, e, env):
        map = self.visit(e.map, env)
        key = self.visit(e.key, env)
        res = self.apply(map["default"], ((), ()), env)
        for (k, v) in map["mapping"]:
            res = z3.If(k == key, v, res)
        return res
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

def mkvar(ctx, solver, collection_depth, type):
    if type == TInt() or type == TLong():
        return z3.Int(fresh_name(), ctx=ctx)
    elif type == TBool():
        return z3.Bool(fresh_name(), ctx=ctx)
    elif isinstance(type, TBitVec):
        return z3.BitVec(fresh_name(), type.width, ctx=ctx)
    elif isinstance(type, TEnum):
        ncases = len(type.cases)
        n = z3.Int(fresh_name(), ctx=ctx)
        solver.add(n >= 0)
        solver.add(n < ncases)
        return n
    elif isinstance(type, TBag):
        mask = [mkvar(ctx, solver, collection_depth, TBool()) for i in range(collection_depth)]
        elems = [mkvar(ctx, solver, collection_depth, type.t) for i in range(collection_depth)]
        # symmetry breaking
        for i in range(len(mask) - 1):
            solver.add(z3.Implies(mask[i], mask[i+1], ctx))
        return (mask, elems)
    elif isinstance(type, TRecord):
        return { field : mkvar(ctx, solver, collection_depth, t) for (field, t) in type.fields }
    elif isinstance(type, THandle):
        h = z3.Int(fresh_name(), ctx)
        return (h, mkvar(ctx, solver, collection_depth, type.value_type))
    else:
        raise NotImplementedError(type)

def mkconst(ctx, solver, val):
    if type(val) == int:
        return z3.IntVal(val, ctx)
    elif type(val) == bool:
        return z3.BoolVal(val, ctx)
    elif type(val) == tuple:
        return ([z3.BoolVal(True, ctx) for x in val], [mkconst(ctx, solver, x) for x in val])
    else:
        raise NotImplementedError(repr(val))

def satisfy(e, collection_depth : int = 2, validate_model : bool = True):
    print("sat? {}".format(pprint(e)))
    # print(repr(e))

    ctx = z3.Context()
    solver = z3.Solver(ctx=ctx)
    visitor = ToZ3(ctx)

    def reconstruct(model, value, type):
        if type == TInt() or type == TLong():
            return model.eval(value, model_completion=True).as_long()
        if type == TBool():
            return bool(model.eval(value, model_completion=True))
        if isinstance(type, TBitVec):
            return model.eval(value, model_completion=True).as_long()
        elif isinstance(type, TBag):
            mask, elems = value
            real_val = ()
            for i in range(len(elems)):
                if reconstruct(model, mask[i], TBool()):
                    real_val += (reconstruct(model, elems[i], type.t),)
            return real_val
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
        else:
            raise NotImplementedError(type)

    _env = { }
    fvs = free_vars(e)
    for v in fvs:
        # print("{} : {}".format(pprint(v), pprint(v.type)))
        _env[v.id] = mkvar(ctx, solver, collection_depth, v.type)
    # print(_env)

    solver.add(visitor.visit(e, _env))
    # print(solver.assertions())
    res = solver.check()
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
        # print(res)
        if validate_model:
            import evaluation
            x = evaluation.eval(e, res)
            if x is not True:
                print("bad example: {}".format(res))
                print(" ---> got {}".format(repr(x)))
                print(" ---> model: {}".format(model))
                print(" ---> assertions: {}".format(solver.assertions()))
                raise Exception()
        return res

class ToZ3WithUninterpretedHoles(ToZ3):
    def __init__(self, z3ctx, z3solver):
        super().__init__(z3ctx)
        # self.collectionsort = z3.DeclareSort("Collection", z3ctx)
        # self.holes = { }
        self.solver = z3solver
    # def flatten(self, value):
    #     if isinstance(value, z3.ExprRef):
    #         yield value
    #     else:
    #         yield z3.Const(fresh_name(), self.collectionsort)
    # def mksort(self, type):
    #     if isinstance(type, TInt) or isinstance(type, TLong):
    #         return z3.IntSort(self.ctx)
    #     elif isinstance(type, TBool):
    #         return z3.BoolSort(self.ctx)
    #     else:
    #         return self.collectionsort
    def visit_EHole(self, e, env):
        # values = tuple(itertools.chain(*(self.flatten(val) for (name, val) in sorted(env.items()))))
        # hole = self.holes.get(e.name)
        # if hole is None:
        #     hole = z3.Function(fresh_name(e.name), *[v.sort() for v in values], self.mksort(e.type))
        #     self.holes[e.name] = hole
        # return hole(*values)
        return mkvar(self.ctx, self.solver, 2, e.type)

def feasible(spec, examples):
    return True # TODO
    if not examples:
        return True

    # print("feasible? {}".format(pprint(spec)))

    ctx = z3.Context()
    solver = z3.Solver(ctx=ctx)
    visitor = ToZ3WithUninterpretedHoles(ctx, solver)

    for ex in examples:
        env = { }
        for name, val in ex.items():
            env[name] = mkconst(ctx, solver, val)
        solver.add(visitor.visit(spec, env))

    # print(solver.assertions())
    return solver.check() == z3.sat
