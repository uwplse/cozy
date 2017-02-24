from cozy.target_syntax import *
from cozy.syntax_tools import BottomUpExplorer, pprint, equal, fresh_var, mk_lambda

def P(e):
    """
    Estimate probability that e evaluates to true.
    """
    if isinstance(e, EUnaryOp) and e.op == UOp.Not:
        return 1 - P(e.e)
    elif isinstance(e, EBool):
        return 1 if e.val else 0
    elif isinstance(e, EBinOp):
        if e.op == BOp.And:
            return P(e.e1) * P(e.e2)
        elif e.op == BOp.Or:
            return 1 - (1 - P(e.e1)) * (1 - P(e.e2))
    return 0.5

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
    def __init__(self, st={}):
        self.st = st
    def visit_EVar(self, v):
        mapping = self.st.get(v)
        if mapping is not None:
            return self.visit(mapping)
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
    def visit_EMakeMap2(self, e):
        return self.visit(e.e)
    def visit_EMapGet(self, e, k=None):
        # return self.visit(e.map) / 3
        if not k:
            k = lambda x: x
        if isinstance(e.map, EMakeMap):
            # return self.visit(e.map) / 3
            return self.visit(k(e.map.value.apply_to(EFilter(e.map.e, ELambda(e.map.key.arg, equal(e.map.key.body, e.key))))))
        elif isinstance(e.map, EMakeMap2):
            return self.visit(k(e.map.value.apply_to(e.key)))
        elif isinstance(e.map, EVar) and e.map in self.st:
            return self.visit(k(EMapGet(self.st[e.map], e.key)))
        elif isinstance(e.map, EMapGet):
            return self.visit_EMapGet(e.map, k=lambda x: EMapGet(x, e.key))
        elif isinstance(e.map, EStateVar):
            return self.visit(k(EMapGet(e.map.e, e.key)))
        else:
            raise NotImplementedError(pprint(e))
    def visit_EFilter(self, e):
        if isinstance(e.e, EFilter):
            return self.visit(EFilter(e.e.e, ELambda(e.p.arg, EAll([e.p.body, e.e.p.apply_to(e.p.arg)]))))
        return self.visit(e.e) * P(e.p.body)
    def visit_EBinOp(self, e):
        if e.op == "+":
            return self.visit(e.e1) + self.visit(e.e2)
        elif e.op == "-":
            return max(self.visit(e.e1) - self.visit(e.e2), 0)
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
    def visit_EStateVar(self, e):
        return self.visit(e.e)
    def visit_Exp(self, e):
        raise NotImplementedError(e)

class MemoryUsageCostModel(CostModel, BottomUpExplorer):
    def __init__(self):
        self.cardinality = CardinalityVisitor().visit
    def cost(self, e):
        cost = self.cardinality(e) / 100 if isinstance(e.type, TBag) or isinstance(e.type, TMap) or isinstance(e.type, TSet) else 0
        cost += e.size() / 100
        return cost
    def is_monotonic(self):
        return False

class RunTimeCostModel(CostModel, BottomUpExplorer):
    def __init__(self):
        self.memcm = MemoryUsageCostModel()
        self.cardinality = CardinalityVisitor().visit
    def cost(self, e):
        return self.visit(e)
    def is_monotonic(self):
        return True

    def visit_EVar(self, e):
        return 1
    def visit_EUnaryOp(self, e):
        cost = self.visit(e.e)
        if e.op in (UOp.Sum, UOp.Distinct):
            cost += self.cardinality(e.e)
        return cost + 0.01
    def visit_EBinOp(self, e):
        if e.op == BOp.In:
            return self.visit(EFilter(e.e2, mk_lambda(e.e1.type, lambda x: equal(x, e.e1))))
        c1 = self.visit(e.e1)
        c2 = self.visit(e.e2)
        cost = c1 + c2
        if e.op == "==" and isinstance(e.e1.type, TBag):
            cost += self.cardinality(e.e1) + self.cardinality(e.e2)
        elif e.op == "-" and isinstance(e.type, TBag):
            cost += self.cardinality(e.e1) + self.cardinality(e.e2)
        # elif e.op == "or":
        #     cost = c1 + P(ENot(e.e1)) * c2
        # elif e.op == "and":
        #     cost = c1 + P(e.e1) * c2
        return cost + 0.01
    # def visit_ECond(self, e):
    #     c1 = self.visit(e.cond)
    #     c2 = self.visit(e.then_branch)
    #     c3 = self.visit(e.else_branch)
    #     p = P(e.cond)
    #     return 0.01 + c1 + p*c2 + (1-p)*c3
    def visit_EMap(self, e):
        return 0.01 + self.visit(e.e) + self.cardinality(e.e) * self.visit(e.f.body)
    def visit_EFlatMap(self, e):
        return 0.01 + self.visit(EMap(e.e, e.f))
    def visit_EFilter(self, e):
        return 0.01 + self.visit(e.e) + self.cardinality(e.e) * self.visit(e.p.body)
    def visit_EMakeMap(self, e):
        return float("inf")
        # return self.visit(e.e) + self.cardinality(e.e) * (self.visit(e.key.body) + self.visit(e.value.body))
    def visit_EMakeMap2(self, e):
        return float("inf")
    def visit_EStateVar(self, e):
        return self.memcm.cost(e)
    def join(self, x, child_costs):
        if isinstance(x, list) or isinstance(x, tuple):
            return sum(child_costs)
        if not isinstance(x, Exp):
            return 0
        return 0.01 + sum(child_costs)

class CompositeCostModel(RunTimeCostModel):
    def __init__(self, state_vars : [EVar]):
        super().__init__()
