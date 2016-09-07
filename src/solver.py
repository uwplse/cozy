from collections import defaultdict

import z3

from syntax import *
from syntax_tools import pprint, free_vars
from common import declare_case, fresh_name, Visitor, FrozenDict

# TODO: Int==Bv32, Long==Bv64
TBitVec = declare_case(Type, "TBitVec", ["width"])

def satisfy(e, collection_depth=2):
    print("sat? {}".format(pprint(e)))
    # print(repr(e))

    ctx = z3.Context()
    solver = z3.Solver(ctx=ctx)

    def mkvar(type):
        if type == TInt() or type == TLong():
            return z3.Int(fresh_name(), ctx=ctx)
        if type == TBool():
            return z3.Bool(fresh_name(), ctx=ctx)
        if isinstance(type, TBitVec):
            return z3.BitVec(fresh_name(), type.width, ctx=ctx)
        elif isinstance(type, TBag):
            mask = [mkvar(TBool()) for i in range(collection_depth)]
            elems = [mkvar(type.t) for i in range(collection_depth)]
            # symmetry breaking
            for i in range(len(mask) - 1):
                solver.add(z3.Implies(mask[i], mask[i+1], ctx))
            return (mask, elems)
        elif isinstance(type, TRecord):
            return { field : mkvar(t) for (field, t) in type.fields }
        else:
            raise NotImplementedError(type)

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
        _env[v.id] = mkvar(v.type)
    # print(_env)

    class V(Visitor):
        def visit_EVar(self, v, env):
            return env[v.id]
        def visit_ENum(self, n, env):
            return n.val
        def visit_EUnaryOp(self, e, env):
            if e.op == "not":
                return z3.Not(self.visit(e.e, env), ctx=ctx)
            elif e.op == "sum":
                bag_mask, bag_elems = self.visit(e.e, env)
                sum = 0
                for i in range(len(bag_elems)):
                    sum = z3.If(bag_mask[i], bag_elems[i], 0, ctx=ctx) + sum
                return sum
            else:
                raise NotImplementedError(e.op)
        def visit_EGetField(self, e, env):
            r = self.visit(e.e, env)
            return r[e.f]
        def visit_EBinOp(self, e, env):
            if e.op == "and":
                return z3.And(self.visit(e.e1, env), self.visit(e.e2, env), ctx=ctx)
            elif e.op == "or":
                return z3.Or(self.visit(e.e1, env), self.visit(e.e2, env), ctx=ctx)
            elif e.op == "==":
                return self.visit(e.e1, env) == self.visit(e.e2, env)
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
                    incl_this = z3.And(bag_mask[i], self.visit(c.e, env), ctx)
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
                    res_mask += [z3.And(incl_this, bit, ctx) for bit in bag2_mask]
                    res_elems += bag2_elems
                return res_mask, res_elems
        def visit_Exp(self, e, *args):
            raise NotImplementedError("toZ3({})".format(e))
        def visit_AstRef(self, e, env):
            """AstRef is the Z3 AST node type"""
            return e

    solver.add(V().visit(e, _env))
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
        return res
