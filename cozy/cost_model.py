from cozy.target_syntax import *
from cozy.syntax_tools import BottomUpExplorer, pprint, equal, fresh_var, mk_lambda
from cozy.rep_inference import infer_rep

class CostModel(object):
    def cost(self, e):
        raise NotImplementedError()
    def is_monotonic(self):
        raise NotImplementedError()

class ConstantCost(CostModel):
    def cost(self, e):
        return 1
    def is_monotonic(self):
        return True

class CardinalityVisitor(BottomUpExplorer):
    def visit_EVar(self, v):
        return 1000
    def visit_EGetField(self, e):
        return 1000
    def visit_ETupleGet(self, e):
        return 1000
    def visit_EEmptyList(self, e):
        return 0
    def visit_ESingleton(self, e):
        return 1
    def visit_EMakeMap(self, e):
        return self.visit(e.e)
    def visit_EMapGet(self, e):
        return self.visit(e.map) / 3
    def visit_EFilter(self, e):
        if e.p.body == EBool(True):
            return self.visit(e.e)
        if e.p.body == EBool(False):
            return 0
        return self.visit(e.e) / 2
    def visit_EBinOp(self, e):
        if e.op == "+":
            return self.visit(e.e1) + self.visit(e.e2)
        elif e.op == "-":
            return self.visit(e.e1) - self.visit(e.e2)
        else:
            raise NotImplementedError(e)
    def visit_EUnaryOp(self, e):
        if e.op == UOp.The:
            return 1000 # TODO???
        elif e.op == UOp.Distinct:
            return self.visit(e.e) * 0.9
        else:
            raise NotImplementedError(e)
    def visit_EMap(self, e):
        return self.visit(e.e)
    def visit_EMapKeys(self, e):
        return self.visit(e.e) * 0.9
    def visit_EFlatMap(self, e):
        return self.visit(e.e) * self.visit(e.f.body)
    def visit_ECond(self, e):
        # This rule is strange, but it has to work this way to preserve monotonicity
        return self.visit(e.then_branch) + self.visit(e.else_branch)
    def visit_Exp(self, e):
        raise NotImplementedError(e)

cardinality = CardinalityVisitor().visit

class MemoryUsageCostModel(CostModel, BottomUpExplorer):
    def cost(self, e):
        return e.size() / 100
        try:
            return self.visit(e) + e.size() / 100
        except:
            print("estimating memory usage of {}".format(pprint(e)))
            raise
    def is_monotonic(self):
        return True

    def visit_EVar(self, e):
        if isinstance(e.type, TBag):
            return cardinality(e)
        return 1
    def visit_EUnaryOp(self, e):
        if e.op == UOp.Sum:
            return 1 # TODO: sizeof(int)
        if e.op == UOp.Not:
            return 1 # TODO: sizeof(bool)
        if e.op == UOp.The:
            return 1 # TODO: sizeof(e.type)
        raise NotImplementedError(e.op)
    def visit_EBool(self, e):
        return 1 # TODO: sizeof(bool)
    def visit_EBinOp(self, e):
        if e.op == "+" and isinstance(e.e1.type, TBag):
            return 0.01 + cardinality(e.e1) + cardinality(e.e2)
        if e.op == "-" and isinstance(e.e1.type, TBag):
            return 0.01 + cardinality(e.e1) + cardinality(e.e2)
        return 1 # TODO: sizeof(e.type)
    def visit_ESingleton(self, e):
        return self.visit(e.e)
    def visit_EEmptyList(self, e):
        return 0
    def visit_EMap(self, e):
        return cardinality(e.e) * self.visit(e.f.body)
    def visit_EFlatMap(self, e):
        return cardinality(e.e) * self.visit(e.f.body)
    def visit_EFilter(self, e):
        return cardinality(e) # TODO: c * sizeof(e.type.t)
    def visit_EMakeMap(self, e):
        return self.visit(e.value.body)
    def visit_EMapGet(self, e):
        assert isinstance(e.map, EMakeMap)
        return self.visit(e.map.value.apply_to(EFilter(e.map.e, ELambda(e.map.key.arg, equal(e.map.key.arg, fresh_var(e.map.key.arg.type))))))
    def visit_EAlterMaybe(self, e):
        return self.visit(e.f.body)
    def visit_EGetField(self, e):
        return 1 # TODO: sizeof(e.type)
    def visit_ENum(self, e):
        return 1 # TODO: sizeof(int)
    def visit_EEnumEntry(self, e):
        return 1 # TODO: sizeof(enum)
    def visit_ECall(self, e):
        return 1 # TODO: sizeof(e.type), or cardinality estimation
    def visit_ETupleGet(self, e):
        return 1 # TODO: sizeof(e.type), or cardinality estimation
    def visit_EGetField(self, e):
        return 1 # TODO: sizeof(e.type), or cardinality estimation
    def visit_ECond(self, e):
        return max(self.visit(e.then_branch), self.visit(e.else_branch))
    def visit_Exp(self, e):
        raise NotImplementedError(repr(e))

class RunTimeCostModel(CostModel, BottomUpExplorer):
    def cost(self, e):
        return self.visit(e)
    def is_monotonic(self):
        return True

    def visit_EVar(self, e):
        return 1
    def visit_EUnaryOp(self, e):
        cost = self.visit(e.e)
        if e.op in (UOp.Sum, UOp.Distinct):
            cost += cardinality(e.e)
        return cost + 0.01
    def visit_EBinOp(self, e):
        if e.op == BOp.In:
            return self.visit(EFilter(e.e2, mk_lambda(e.e1.type, lambda x: equal(x, e.e1))))
        cost = self.visit(e.e1) + self.visit(e.e2)
        if e.op == "==" and isinstance(e.e1.type, TBag):
            cost += cardinality(e.e1) + cardinality(e.e2)
        return cost + 0.01
    def visit_EMap(self, e):
        return 0.01 + self.visit(e.e) + cardinality(e.e) * self.visit(e.f.body)
    def visit_EFlatMap(self, e):
        return 0.01 + self.visit(EFlatten(EMap(e.e, e.f)))
    def visit_EFilter(self, e):
        return 0.01 + self.visit(e.e) + cardinality(e.e) * self.visit(e.p.body)
    def visit_EMakeMap(self, e):
        return float("inf")
        # return self.visit(e.e) + cardinality(e.e) * (self.visit(e.key.body) + self.visit(e.value.body))
    def join(self, x, child_costs):
        if isinstance(x, list) or isinstance(x, tuple):
            return sum(child_costs)
        if not isinstance(x, Exp):
            return 0
        return 0.01 + sum(child_costs)

class CompositeCostModel(CostModel):
    def __init__(self, state_vars : [EVar]):
        self.state_vars = state_vars
        self.rtcm = RunTimeCostModel()
        self.memcm = MemoryUsageCostModel()
        self.factor = 0.01 # 0 = only care about runtime, 1 = only care about memory
    def __repr__(self):
        return "CompositeCostModel({})".format(repr(self.state_vars))
    def is_monotonic(self):
        return self.rtcm.is_monotonic() and self.memcm.is_monotonic()
    def split_cost(self, st, e):
        return (1-self.factor) * self.rtcm.cost(e) + self.factor * sum(self.memcm.cost(proj) for (v, proj) in st)
    def cost(self, e):
        try:
            return min((self.split_cost(rep, e2) for (rep, e2) in infer_rep(self.state_vars, e)),
                default=float("inf"))
        except:
            print("cost evaluation failed for {}".format(pprint(e)))
            print(repr(e))
            for (rep, e2) in infer_rep(self.state_vars, e):
                try:
                    self.split_cost(rep, e2)
                except Exception as exc:
                    print("-" * 20 + " EXCEPTION: {}".format(repr(exc)))
                    for (v, proj) in rep:
                        print("  {} : {} = {}".format(v.id, pprint(v.type), pprint(proj)))
                    print("  return {}".format(repr(e2)))
            raise
