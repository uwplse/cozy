from cozy.target_syntax import *
from cozy.syntax_tools import BottomUpExplorer, pprint, equal, fresh_var, mk_lambda
from cozy.rep_inference import infer_rep

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
    def __init__(self, st):
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
    def visit_EMapGet(self, e):
        if isinstance(e.map, EMakeMap):
            # return self.visit(e.map) / 3
            return self.visit(e.map.value.apply_to(EFilter(e.map.e, ELambda(e.map.key.arg, equal(e.map.key.body, e.key)))))
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
    def visit_Exp(self, e):
        raise NotImplementedError(e)
    def __call__(self, e):
        return self.visit(e)

class MemoryUsageCostModel(CostModel, BottomUpExplorer):
    def __init__(self):
        self.cardinality = CardinalityVisitor({})
    def cost(self, e):
        # return e.size()
        cost = self.cardinality(e) / 100 if isinstance(e.type, TBag) or isinstance(e.type, TMap) or isinstance(e.type, TSet) else 0
        cost += e.size() / 100
        return cost
    def is_monotonic(self):
        return False

class RunTimeCostModel(CostModel, BottomUpExplorer):
    def __init__(self):
        self.cardinality = lambda e: 0
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
        return 0.01 + self.visit(EFlatten(EMap(e.e, e.f)))
    def visit_EFilter(self, e):
        return 0.01 + self.visit(e.e) + self.cardinality(e.e) * self.visit(e.p.body)
    def visit_EMakeMap(self, e):
        return float("inf")
        # return self.visit(e.e) + self.cardinality(e.e) * (self.visit(e.key.body) + self.visit(e.value.body))
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
        self.factor = 0.001 # 0 = only care about runtime, 1 = only care about memory
    def __repr__(self):
        return "CompositeCostModel({})".format(repr(self.state_vars))
    def is_monotonic(self):
        return self.rtcm.is_monotonic() and self.memcm.is_monotonic()
    def split_cost(self, st, e):
        self.rtcm.cardinality = CardinalityVisitor(dict(st))
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
