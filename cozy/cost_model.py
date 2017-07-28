from collections import OrderedDict
from functools import total_ordering, lru_cache
import itertools
import sys

from cozy.common import typechecked, partition
from cozy.target_syntax import *
from cozy.syntax_tools import BottomUpExplorer, pprint, equal, fresh_var, mk_lambda, free_vars, subst
from cozy.pools import RUNTIME_POOL, STATE_POOL
from cozy.solver import valid, satisfiable, REAL, SolverReportedUnknown
from cozy.evaluation import eval

class CostModel(object):
    def cost(self, e, pool):
        raise NotImplementedError()
    def is_monotonic(self):
        raise NotImplementedError()

@lru_cache(maxsize=2**16)
@typechecked
def cardinality_le(c1 : Exp, c2 : Exp, assumptions : Exp) -> bool:
    assert c1.type == c2.type
    v = fresh_var(c1.type.t)
    return valid(EImplies(assumptions, EImplies(EIn(v, c1), EIn(v, c2))))

@lru_cache(maxsize=2**16)
@typechecked
def cardinality_le_implies_lt(c1 : Exp, c2 : Exp, assumptions : Exp) -> bool:
    assert c1.type == c2.type
    v = fresh_var(c1.type.t)
    return satisfiable(EAll((assumptions, EIn(v, c2), ENot(EIn(v, c1)))))

class Cost(object):

    WORSE = "worse"
    BETTER = "better"
    UNORDERED = "unordered"

    def __init__(self,
            e             : Exp,
            pool          : int,
            formula       : Exp,
            secondary     : float          = 0.0,
            assumptions   : Exp            = T,
            cardinalities : { EVar : Exp } = None):
        assert formula.type == INT
        self.e = e
        self.pool = pool
        self.formula = formula
        self.secondary = secondary
        assert all(v.type == INT for v in free_vars(assumptions))
        self.assumptions = assumptions
        self.cardinalities = cardinalities or { }

    def order_cardinalities(self, other, assumptions):
        cardinalities = OrderedDict()
        cardinalities.update(self.cardinalities)
        cardinalities.update(other.cardinalities)
        assumptions = EAll((self.assumptions, other.assumptions, assumptions))
        res = []
        for (v1, c1) in cardinalities.items():
            res.append(EBinOp(v1, ">=", ZERO).with_type(BOOL))
            for (v2, c2) in cardinalities.items():
                if v1 == v2 or c1.type != c2.type:
                    continue
                if cardinality_le(c1, c2, assumptions):
                    if cardinality_le_implies_lt(c1, c2, assumptions):
                        res.append(EBinOp(v1, "<", v2).with_type(BOOL))
                    else:
                        res.append(EBinOp(v1, "<=", v2).with_type(BOOL))
        # print("cards: {}".format(pprint(EAll(res))))
        return EAll(res)

    @typechecked
    def always(self, op, other, assumptions : Exp) -> bool:
        """
        Partial order on costs subject to assumptions.
        """
        if isinstance(self.formula, ENum) and isinstance(other.formula, ENum):
            return eval(EBinOp(self.formula, op, other.formula).with_type(BOOL), env={})
        f = EImplies(
            EAll((self.assumptions, other.assumptions, self.order_cardinalities(other, assumptions))),
            EBinOp(self.formula, op, other.formula).with_type(BOOL))
        try:
            return valid(f, logic="QF_LIA", timeout=1)
        except SolverReportedUnknown:
            # If we accidentally made an unsolveable integer arithmetic formula,
            # then try again with real numbers. This will admit some models that
            # are not possible (since bags must have integer cardinalities), but
            # returning false is always a safe move here, so it's fine.
            print("Warning: not able to solve {}".format(pprint(f)), file=sys.stderr)
            f = subst(f, { v.id : EVar(v.id).with_type(REAL) for v in free_vars(f) })
            return valid(f, logic="QF_NRA")

    def compare_to(self, other, assumptions : Exp = T) -> bool:
        if self.sometimes_worse_than(other, assumptions) and not other.sometimes_worse_than(self, assumptions):
            return Cost.WORSE
        elif self.sometimes_better_than(other, assumptions) and not other.sometimes_better_than(self, assumptions):
            return Cost.BETTER
        else:
            if self.always("==", other, assumptions):
                return (
                    Cost.WORSE if self.secondary > other.secondary else
                    Cost.BETTER if self.secondary < other.secondary else
                    Cost.UNORDERED)
            return Cost.UNORDERED

    def always_worse_than(self, other, assumptions : Exp = T) -> bool:
        # it is NOT possible that `self` takes less time than `other`
        return self.always(">", other, assumptions)

    def always_better_than(self, other, assumptions : Exp = T) -> bool:
        # it is NOT possible that `self` takes more time than `other`
        return self.always("<", other, assumptions)

    def sometimes_worse_than(self, other, assumptions : Exp = T) -> bool:
        # it is possible that `self` takes more time than `other`
        return not self.always("<=", other, assumptions)

    def sometimes_better_than(self, other, assumptions : Exp = T) -> bool:
        # it is possible that `self` takes less time than `other`
        return not self.always(">=", other, assumptions)

    # def equivalent_to(self, other, assumptions : Exp = T) -> bool:
    #     return not self.always_worse_than(other) and not other.always_worse_than(self)

    def __str__(self):
        return "cost[{} subject to {}, {}]".format(
            pprint(self.formula),
            pprint(self.assumptions),
            ", ".join(pprint(EEq(v, EUnaryOp(UOp.Length, e))) for v, e in self.cardinalities.items()))

    def __repr__(self):
        return "Cost({!r}, assumptions={!r}, cardinalities={!r})".format(
            self.formula,
            self.assumptions,
            self.cardinalities)

Cost.ZERO = Cost(None, None, ZERO)

def break_sum(e):
    if isinstance(e, EBinOp) and e.op == "+":
        yield from break_sum(e.e1)
        yield from break_sum(e.e2)
    else:
        yield e

def ESum(es):
    es = [e for x in es for e in break_sum(x) if e != ZERO]
    if not es:
        return ZERO
    nums, nonnums = partition(es, lambda e: isinstance(e, ENum))
    es = nonnums
    if nums:
        es.append(ENum(sum(n.val for n in nums)).with_type(INT))

    def balance(es):
        if len(es) < 4:
            res = es[0]
            for i in range(1, len(es)):
                res = EBinOp(res, "+", es[i]).with_type(res.type)
            return res
        else:
            cut = len(es) // 2
            return EBinOp(balance(es[:cut]), "+", balance(es[cut:])).with_type(INT)

    return balance(es)

# Some kinds of expressions have a massive penalty associated with them if they
# appear at runtime.
EXTREME_COST = ENum(1000).with_type(INT)
MILD_PENALTY = ENum(  10).with_type(INT)
TWO          = ENum(   2).with_type(INT)

class CompositeCostModel(CostModel, BottomUpExplorer):
    def __init__(self):
        super().__init__()
    def __repr__(self):
        return "CompositeCostModel()"
    def cardinality(self, e : Exp, plus_one=False) -> Exp:
        if plus_one:
            return ESum((self.cardinality(e, plus_one=False), ONE))
        if isinstance(e, EEmptyList):
            return ZERO
        if isinstance(e, ESingleton):
            return ONE
        if isinstance(e, EBinOp) and e.op == "+":
            return ESum((self.cardinality(e.e1), self.cardinality(e.e2)))
        if isinstance(e, EMap):
            return self.cardinality(e.e)
        if e in self.cardinalities:
            return self.cardinalities[e]
        else:
            v = fresh_var(INT)
            self.cardinalities[e] = v
            if isinstance(e, EFilter):
                self.assumptions.append(EBinOp(v, "<=", self.cardinality(e.e)).with_type(BOOL))
            return v
    def statecost(self, e : Exp) -> float:
        return e.size() / 100
    def visit_EStateVar(self, e):
        self.secondaries += self.statecost(e.e)
        return ONE
    def visit_EUnaryOp(self, e):
        costs = [ONE, self.visit(e.e)]
        if e.op in (UOp.Sum, UOp.Distinct, UOp.AreUnique):
            costs.append(self.cardinality(e.e))
        return ESum(costs)
    def visit_EBinOp(self, e):
        c1 = self.visit(e.e1)
        c2 = self.visit(e.e2)
        costs = [ONE, c1, c2]
        if e.op == BOp.In:
            costs.append(self.cardinality(e.e2))
        elif e.op == "==" and isinstance(e.e1.type, TBag):
            costs.append(self.cardinality(e.e1))
            costs.append(self.cardinality(e.e2))
        elif e.op == "-" and isinstance(e.type, TBag):
            costs.append(self.cardinality(e.e1))
            costs.append(self.cardinality(e.e2))
        return ESum(costs)
    def visit_EMakeMap2(self, e):
        return ESum((EXTREME_COST, self.visit(e.e), EBinOp(self.cardinality(e.e, plus_one=True), "*", self.visit(e.value.body)).with_type(INT)))
    def visit_EFilter(self, e):
        return ESum((TWO, self.visit(e.e), EBinOp(self.cardinality(e.e, plus_one=True), "*", self.visit(e.p.body)).with_type(INT)))
    def visit_EFlatMap(self, e):
        return self.visit(EMap(e.e, e.f))
    def visit_EMap(self, e):
        return ESum((TWO, self.visit(e.e), EBinOp(self.cardinality(e.e, plus_one=True), "*", self.visit(e.f.body)).with_type(INT)))
    def join(self, x, child_costs):
        if isinstance(x, list) or isinstance(x, tuple):
            return ESum(child_costs)
        if not isinstance(x, Exp):
            return ZERO
        return ESum(itertools.chain((ONE,), child_costs))
    def is_monotonic(self):
        return False
    def cost(self, e, pool):
        if pool == RUNTIME_POOL:
            self.cardinalities = OrderedDict()
            self.assumptions = []
            self.secondaries = 0
            f = self.visit(e)
            invcard = OrderedDict()
            for e, v in self.cardinalities.items():
                invcard[v] = e
            return Cost(e, pool, f, secondary=self.secondaries, assumptions=EAll(self.assumptions), cardinalities=invcard)
        else:
            return Cost(e, pool, ZERO, secondary=self.statecost(e))
