from collections import OrderedDict
from functools import total_ordering, lru_cache
import itertools

from cozy.common import typechecked, partition, make_random_access
from cozy.target_syntax import *
from cozy.syntax_tools import BottomUpExplorer, pprint, equal, fresh_var, mk_lambda, free_vars, subst, alpha_equivalent, all_exps, cse
from cozy.typecheck import is_collection
from cozy.pools import RUNTIME_POOL, STATE_POOL
from cozy.solver import valid, satisfiable, REAL, SolverReportedUnknown, IncrementalSolver
from cozy.evaluation import eval
from cozy.opts import Option

assume_large_cardinalities = Option("assume-large-cardinalities", int, 1000)
integer_cardinalities = Option("try-integer-cardinalities", bool, True)

# In principle these settings are supposed to improve performance; in practice,
# they do not.
incremental = False
use_indicators = False

class Cost(object):
    WORSE = "worse"
    BETTER = "better"
    UNORDERED = "unordered"
    def compare_to(self, other, assumptions : Exp = T, solver : IncrementalSolver = None):
        raise NotImplementedError()

class CostModel(object):
    def cost(self, e, pool):
        raise NotImplementedError()
    def is_monotonic(self):
        raise NotImplementedError()

# -----------------------------------------------------------------------------

class SymbolicCost(Cost):
    @typechecked
    def __init__(self, formula : Exp, cardinalities : { Exp : EVar }, heuristics : [Exp]):
        self.formula = formula
        self.cardinalities = cardinalities
        self.heuristics = list(heuristics)
    def __repr__(self):
        return "SymbolicCost({!r}, {!r})".format(self.formula, self.cardinalities)
    def __str__(self):
        return pprint(self.formula)
    def compare_to(self, other, assumptions : Exp = T, solver : IncrementalSolver = None):
        assert isinstance(other, SymbolicCost)
        if False:
            s = IncrementalSolver()
            v1, v2 = fresh_var(BOOL), fresh_var(BOOL)
            s.add_assumption(EAll(self.heuristics + [
                self.order_cardinalities(other, assumptions, solver),
                EEq(v1, EBinOp(self.formula, "<=", other.formula).with_type(BOOL)),
                EEq(v2, EBinOp(other.formula, "<=", self.formula).with_type(BOOL))]))
            o1 = s.valid(v1)
            o2 = s.valid(v2)
        else:
            cards = self.order_cardinalities(other, assumptions, solver)
            o1 = self.always("<=", other, cards=cards)
            o2 = other.always("<=", self, cards=cards)
        if o1 and not o2:
            return Cost.BETTER
        elif o2 and not o1:
            return Cost.WORSE
        else:
            return Cost.UNORDERED
    def order_cardinalities(self, other, assumptions : Exp = T, solver : IncrementalSolver = None) -> Exp:
        if incremental and solver is None:
            solver = IncrementalSolver()
        if incremental:
            solver.push()
            solver.add_assumption(assumptions)

        cardinalities = OrderedDict()
        for m in (self.cardinalities, other.cardinalities):
            for k, v in m.items():
                cardinalities[v] = k

        conds = []
        res = []
        for (v1, c1) in cardinalities.items():
            res.append(EBinOp(v1, ">=", ZERO).with_type(BOOL))
            for (v2, c2) in cardinalities.items():
                if v1 == v2:
                    continue
                if alpha_equivalent(c1, c2):
                    res.append(EEq(v1, v2))
                    continue

                if incremental and use_indicators:
                    conds.append((v1, v2, fresh_var(BOOL), cardinality_le(c1, c2, as_f=True)))
                else:
                    if incremental:
                        le = cardinality_le(c1, c2, solver=solver)
                    else:
                        # print("CMP {}: {} / {}".format("<-" if v1 < v2 else "->", pprint(c1), pprint(c2)))
                        le = cardinality_le(c1, c2, assumptions=assumptions, solver=solver)
                    if le:
                        res.append(EBinOp(v1, "<=", v2).with_type(BOOL))

        if incremental and use_indicators:
            solver.add_assumption(EAll(
                [EEq(indicator, f) for (v1, v2, indicator, f) in conds]))
            for (v1, v2, indicator, f) in conds:
                if solver.valid(indicator):
                    res.append(EBinOp(v1, "<=", v2).with_type(BOOL))

        if incremental:
            solver.pop()

        if assume_large_cardinalities.value:
            min_cardinality = ENum(assume_large_cardinalities.value).with_type(INT)
            for cvar, exp in cardinalities.items():
                if isinstance(exp, EVar):
                    res.append(EBinOp(cvar, ">", min_cardinality).with_type(BOOL))

        # print("cards: {}".format(pprint(EAll(res))))
        return EAll(res)
    @typechecked
    def always(self, op, other, cards : Exp, **kwargs) -> bool:
        """
        Partial order on costs.
        """
        if isinstance(self.formula, ENum) and isinstance(other.formula, ENum):
            return eval(EBinOp(self.formula, op, other.formula).with_type(BOOL), env={})
        f = EImplies(EAll(self.heuristics + [cards]), EBinOp(self.formula, op, other.formula).with_type(BOOL))
        if integer_cardinalities.value:
            try:
                return valid(f, logic="QF_LIA", timeout=1, **kwargs)
            except SolverReportedUnknown:
                # If we accidentally made an unsolveable integer arithmetic formula,
                # then try again with real numbers. This will admit some models that
                # are not possible (since bags must have integer cardinalities), but
                # returning false is always a safe move here, so it's fine.
                print("Warning: not able to solve {}".format(pprint(f)))
        f = subst(f, { v.id : EVar(v.id).with_type(REAL) for v in free_vars(cards) })
        # This timeout is dangerous! Sufficiently complex specifications
        # will cause this to timeout _every_time_, meaning we never make
        # progress.
        #   However, this timeout helps ensure liveness: the Python process
        # never gets deadlocked waiting for Z3. In the Distant Future it
        # would be nice to move away from Z3Py and invoke Z3 as a subprocess
        # instead. That would allow the Python process to break out if it is
        # asked to stop while Z3 is running. It would also give us added
        # protection against Z3 segfaults, which have been observed in the
        # wild from time to time.
        timeout = 60
        try:
            return valid(f, logic="QF_NRA", timeout=timeout, **kwargs)
        except SolverReportedUnknown:
            print("Giving up!")
            return False

class PlainCost(Cost):
    def __init__(self, n : int):
        self.n = n
    def __repr__(self):
        return "PlainCost({!r})".format(self.n)
    def __str__(self):
        return str(self.n)
    def compare_to(self, other, assumptions : Exp = T, solver : IncrementalSolver = None):
        assert isinstance(other, PlainCost)
        if self.n < other.n:
            return Cost.BETTER
        elif self.n > other.n:
            return Cost.WORSE
        else:
            return Cost.UNORDERED

class CompositeCost(Cost):
    def __init__(self, *costs):
        self.costs = tuple(costs)
    def __repr__(self):
        return "CompositeCost({})".format(", ".join(repr(c) for c in self.costs))
    def __str__(self):
        return "; ".join(str(c) for c in self.costs)
    def compare_to(self, other, assumptions : Exp = T, solver : IncrementalSolver = None):
        assert isinstance(other, CompositeCost)
        assert len(self.costs) == len(other.costs)
        i = 0
        for c1, c2 in zip(self.costs, other.costs):
            order = c1.compare_to(c2, assumptions, solver)
            i += 1
            if order != Cost.UNORDERED:
                return order
        return Cost.UNORDERED

# -----------------------------------------------------------------------------

class CompositeCostModel(CostModel):
    def __repr__(self):
        return "CompositeCostModel()"
    def is_monotonic(self):
        return False
    def cost(self, e, pool):
        cards = OrderedDict()
        # for v in free_vars(e):
        #     if is_collection(v.type):
        #         cardinality(v, cards)
        hint_cache = []
        if pool == STATE_POOL:
            return CompositeCost(
                sizeof(e, cards, hint_cache),
                ast_size(e))
        else:
            assert pool == RUNTIME_POOL
            return CompositeCost(
                asymptotic_runtime(e, hint_cache),
                storage_size(e, cards, hint_cache),
                precise_runtime(e, hint_cache),
                ast_size(e))

def maybe_inline(e, f):
    if isinstance(e, ENum) or isinstance(e, EVar):
        return f(e)
    v = fresh_var(e.type, omit=free_vars(f(T)))
    body = f(v)
    return ELet(e, ELambda(v, body)).with_type(body.type)

def EMax(es):
    es = make_random_access(es)
    assert es
    assert all(isinstance(e, Exp) for e in es), es
    res = es[0]
    t = res.type
    fvs = set(v.id for v in free_vars(res))
    for i in range(1, len(es)):
        res = maybe_inline(res,   lambda v1:
              maybe_inline(es[i], lambda v2:
                ECond(EGt(v1, v2), v1, v2).with_type(t)))
        # v1 = fresh_var(res.type, omit=fvs)
        # fvs.add(v1.id)
        # v2 = fresh_var(res.type, omit=fvs)
        # fvs.add(v2.id)
        # fvs |= set(v.id for v in free_vars(es[i]))
        # res = ELet(res,   ELambda(v1,
        #       ELet(es[i], ELambda(v2,
        #         ECond(EGt(v1, v2), v1, v2).with_type(res.type))).with_type(res.type))).with_type(res.type)
        # res = ECond(EGt(res, es[i]), res, es[i]).with_type(res.type)
    return res

def asymptotic_runtime(e, hint_cache):
    class V(BottomUpExplorer):
        def __init__(self):
            super().__init__()
            self.cardinalities = { }
        def EBinOp(self, e1, op, e2):
            if isinstance(e1, list): e1 = EMax([ONE] + e1)
            if isinstance(e2, list): e2 = EMax([ONE] + e2)
            if op == "*":
                if e1 == ENum(1): return e2
                if e2 == ENum(1): return e1
            e = EBinOp(e1, op, e2).with_type(e1.type)
            if isinstance(e1, ENum) and isinstance(e2, ENum):
                return ENum(eval(e, {})).with_type(e1.type)
            return e
        def cardinality(self, e : Exp, **kwargs) -> Exp:
            return cardinality(e, self.cardinalities, hint_cache, **kwargs)
        def combine(self, costs):
            res = []
            q = list(costs)
            while q:
                c = q.pop()
                if isinstance(c, ENum):
                    continue
                elif isinstance(c, Exp):
                    res.append(c)
                else:
                    assert isinstance(c, list) or isinstance(c, tuple), repr(c)
                    q.extend(c)
            return res
            # return EMax([ONE] + res)
        def visit_EStateVar(self, e):
            return self.combine([ONE])
        def visit_EUnaryOp(self, e):
            costs = [ONE, self.visit(e.e)]
            if e.op in (UOp.Sum, UOp.Distinct, UOp.AreUnique, UOp.All, UOp.Any, UOp.Length):
                costs.append(self.cardinality(e.e))
            return self.combine(costs)
        def visit_EBinOp(self, e):
            c1 = self.visit(e.e1)
            c2 = self.visit(e.e2)
            costs = [ONE, c1, c2]
            if e.op == BOp.In:
                costs.append(self.cardinality(e.e2))
            elif e.op == "==" and is_collection(e.e1.type):
                costs.append(self.cardinality(e.e1))
                costs.append(self.cardinality(e.e2))
            elif e.op == "-" and is_collection(e.type):
                costs.append(self.cardinality(e.e1))
                costs.append(self.cardinality(e.e2))
            return self.combine(costs)
        def visit_ELambda(self, e):
            # avoid name collisions with fresh_var
            return self.visit(e.apply_to(fresh_var(e.arg.type)))
        def visit_EMakeMap2(self, e):
            return self.combine([self.EBinOp(self.cardinality(e.e, plus_one=True), "*", self.visit(e.value)).with_type(INT)])
        def visit_EFilter(self, e):
            return self.combine((ONE, self.visit(e.e), self.EBinOp(self.cardinality(e.e, plus_one=True), "*", self.visit(e.p)).with_type(INT)))
        def visit_EFlatMap(self, e):
            return self.visit(EMap(e.e, e.f))
        def visit_EMap(self, e):
            return self.combine((ONE, self.visit(e.e), self.EBinOp(self.cardinality(e.e, plus_one=True), "*", self.visit(e.f)).with_type(INT)))
        def visit_EArgMin(self, e):
            return self.combine((ONE, self.visit(e.e), self.EBinOp(self.cardinality(e.e, plus_one=True), "*", self.visit(e.f)).with_type(INT)))
        def visit_EArgMax(self, e):
            return self.combine((ONE, self.visit(e.e), self.EBinOp(self.cardinality(e.e, plus_one=True), "*", self.visit(e.f)).with_type(INT)))
        def visit_EDropFront(self, e):
            return self.combine((ONE, self.visit(e.e), self.cardinality(e.e, plus_one=True).with_type(INT)))
        def visit_EDropBack(self, e):
            return self.combine((ONE, self.visit(e.e), self.cardinality(e.e, plus_one=True).with_type(INT)))
        def join(self, x, child_costs):
            if isinstance(x, list) or isinstance(x, tuple):
                return self.combine(child_costs)
            if not isinstance(x, Exp):
                return self.combine([ZERO])
            return self.combine(itertools.chain((ONE,), child_costs))
    vis = V()
    f = EMax([ONE] + vis.visit(e))
    # f = cse(f)
    return SymbolicCost(f, vis.cardinalities, hint_cache)

def sizeof(e, cardinalities, hint_cache):
    terms = [ONE]
    if is_collection(e.type):
        terms.append(cardinality(e, cardinalities, hint_cache))
    elif isinstance(e.type, TMap):
        ks = EMapKeys(e).with_type(TBag(e.type.k))
        terms.append(cardinality(ks, cardinalities, hint_cache))
        if is_collection(e.type.v):
            vals = EFlatMap(ks, mk_lambda(e.type.k, lambda k: EMapGet(e, k).with_type(e.type.v))).with_type(e.type.v)
            terms.append(cardinality(vals, cardinalities, hint_cache))
    return SymbolicCost(ESum(terms), cardinalities, hint_cache)

def storage_size(e, cardinalities, hint_cache):
    sizes = []
    for x in all_exps(e):
        if isinstance(x, EStateVar):
            hc = []
            sz_cost = sizeof(x.e, cardinalities, hc)
            sizes.append(sz_cost.formula)
            hint_cache.extend(hc)
    return SymbolicCost(ESum(sizes), cardinalities, hint_cache)

# Some kinds of expressions have a massive penalty associated with them if they
# appear at runtime.
EXTREME_COST    = ENum(1000).with_type(INT)
MILD_PENALTY    = ENum(  10).with_type(INT)
TWO             = ENum(   2).with_type(INT)

def precise_runtime(e, hint_cache):
    class V(BottomUpExplorer):
        def __init__(self):
            super().__init__()
            self.cardinalities = { }
        def cardinality(self, e : Exp, **kwargs) -> Exp:
            return cardinality(e, self.cardinalities, hint_cache, **kwargs)
        def visit_EStateVar(self, e):
            return ONE
        def visit_EUnaryOp(self, e):
            costs = [ONE, self.visit(e.e)]
            if e.op in (UOp.Sum, UOp.Distinct, UOp.AreUnique, UOp.All, UOp.Any, UOp.Length):
                costs.append(self.cardinality(e.e))
            return ESum(costs)
        def visit_EBinOp(self, e):
            c1 = self.visit(e.e1)
            c2 = self.visit(e.e2)
            costs = [ONE, c1, c2]
            if e.op == BOp.In:
                costs.append(self.cardinality(e.e2))
            elif e.op == "==" and is_collection(e.e1.type):
                costs.append(EXTREME_COST)
                costs.append(self.cardinality(e.e1))
                costs.append(self.cardinality(e.e2))
            elif e.op == "-" and is_collection(e.type):
                costs.append(EXTREME_COST)
                costs.append(self.cardinality(e.e1))
                costs.append(self.cardinality(e.e2))
            return ESum(costs)
        def visit_ELambda(self, e):
            # avoid name collisions with fresh_var
            return self.visit(e.apply_to(fresh_var(e.arg.type)))
        def visit_EMapGet(self, e):
            # mild penalty here because we want "x.f" < "map.get(x)"
            return ESum((MILD_PENALTY, self.visit(e.map), self.visit(e.key)))
        def visit_EMakeMap2(self, e):
            return ESum((EXTREME_COST, self.visit(e.e), EBinOp(self.cardinality(e.e, plus_one=True), "*", self.visit(e.value)).with_type(INT)))
        def visit_EFilter(self, e):
            return ESum((TWO, self.visit(e.e), EBinOp(self.cardinality(e.e, plus_one=True), "*", self.visit(e.p)).with_type(INT)))
        def visit_EFlatMap(self, e):
            return self.visit(EMap(e.e, e.f))
        def visit_EMap(self, e):
            return ESum((TWO, self.visit(e.e), EBinOp(self.cardinality(e.e, plus_one=True), "*", self.visit(e.f)).with_type(INT)))
        def visit_EArgMin(self, e):
            return ESum((TWO, self.visit(e.e), EBinOp(self.cardinality(e.e, plus_one=True), "*", self.visit(e.f)).with_type(INT)))
        def visit_EArgMax(self, e):
            return ESum((TWO, self.visit(e.e), EBinOp(self.cardinality(e.e, plus_one=True), "*", self.visit(e.f)).with_type(INT)))
        def visit_EDropFront(self, e):
            return ESum((MILD_PENALTY, self.visit(e.e), self.cardinality(e.e, plus_one=True).with_type(INT)))
        def visit_EDropBack(self, e):
            return ESum((MILD_PENALTY, self.visit(e.e), self.cardinality(e.e, plus_one=True).with_type(INT)))
        def join(self, x, child_costs):
            if isinstance(x, list) or isinstance(x, tuple):
                return ESum(child_costs)
            if not isinstance(x, Exp):
                return ZERO
            return ESum(itertools.chain((ONE,), child_costs))
    vis = V()
    f = vis.visit(e)
    return SymbolicCost(f, vis.cardinalities, hint_cache)

def ast_size(e):
    return PlainCost(e.size())

# -----------------------------------------------------------------------------

# @typechecked
def cardinality(e : Exp, cache : { Exp : EVar }, heuristics : [Exp], plus_one=False) -> Exp:
    """
    Produce a symbolic expression for the cardinality of expression `e`.
    The free variables in the output expression will all be integers.
    Params:
        `e`          - [IN ] the expression
        `cache`      - [OUT] mapping from free variables in output to
                             collections whose cardinalities they track
        `heuristics` - [OUT] hints about free variables in output that help
                             produce a slightly improved cost model
    """
    assert is_collection(e.type)
    # if plus_one:
    #     return ESum((self.cardinality(e, plus_one=False), ONE))
    if isinstance(e, EEmptyList):
        return ZERO
    if isinstance(e, ESingleton):
        return ONE
    if isinstance(e, EBinOp) and e.op == "+":
        return ESum((cardinality(e.e1, cache, heuristics), cardinality(e.e2, cache, heuristics)))
    if isinstance(e, EMap):
        return cardinality(e.e, cache, heuristics)
    if isinstance(e, EStateVar):
        return cardinality(e.e, cache, heuristics)
    prev = cache.get(e)
    if prev is not None:
        return prev
    else:
        v = fresh_var(INT)
        cache[e] = v
        if isinstance(e, EFilter):
            cc = cardinality(e.e, cache, heuristics)
            # heuristics.append(EBinOp(v, "<=", cc).with_type(BOOL))
            # heuristic: (xs) large implies (filter_p xs) large
            heuristics.append(EBinOp(
                EBinOp(v,  "*", ENum(5).with_type(INT)).with_type(INT), ">=",
                EBinOp(cc, "*", ENum(4).with_type(INT)).with_type(INT)).with_type(BOOL))
        if isinstance(e, EUnaryOp) and e.op == UOp.Distinct:
            cc = cardinality(e.e, cache, heuristics)
            # heuristics.append(EBinOp(v, "<=", cc).with_type(BOOL))
            # heuristics.append(EImplies(EGt(cc, ZERO), EGt(v, ZERO)))
            # heuristic: (xs) large implies (distinct xs) large
            heuristics.append(EBinOp(
                EBinOp(v,  "*", ENum(5).with_type(INT)).with_type(INT), ">=",
                EBinOp(cc, "*", ENum(4).with_type(INT)).with_type(INT)).with_type(BOOL))
        # if isinstance(e, EBinOp) and e.op == "-":
        #     heuristics.append(EBinOp(v, "<=", cardinality(e.e1, cache, heuristics)).with_type(BOOL))
        # if isinstance(e, ECond):
        #     heuristics.append(EAny([EEq(v, cardinality(e.then_branch, cache, heuristics)), EEq(v, self.cardinality(e.else_branch))]))
        return v

@lru_cache(maxsize=2**16)
# @typechecked
def cardinality_le(c1 : Exp, c2 : Exp, assumptions : Exp = T, as_f : bool = False, solver : IncrementalSolver = None) -> bool:
    """
    Is |c1| <= |c2|?
    Yes, iff there are no v such that v occurs more times in c2 than in c1.
    """
    if True:
        f = EBinOp(ELen(c1), "<=", ELen(c2)).with_type(BOOL)
    else:
        assert c1.type == c2.type
        # Oh heck.
        # This isn't actually very smart if:
        #   x = [y]
        #   a = Filter (!= y) b
        # This method can't prove that |x| <= |a|, even though |a| is likely huge
        v = fresh_var(c1.type.t)
        f = EBinOp(ECountIn(v, c1), "<=", ECountIn(v, c2)).with_type(BOOL)
    if as_f:
        return f
    res = solver.valid(EImplies(assumptions, f)) if solver else valid(EImplies(assumptions, f))
    # assert res == valid(EImplies(assumptions, f))
    return res

def debug_comparison(e1, c1, e2, c2, assumptions : Exp = T):
    from cozy.syntax_tools import break_conj
    print("-" * 20)
    print("comparing costs...")
    print("  e1 = {}".format(pprint(e1)))
    print("  c1 = {}".format(c1))
    print("  e2 = {}".format(pprint(e2)))
    print("  c2 = {}".format(c2))
    print("  c1 compare_to c2 = {}".format(c1.compare_to(c2, assumptions=assumptions)))
    print("  c2 compare_to c1 = {}".format(c2.compare_to(c1, assumptions=assumptions)))
    for c1, c2 in zip(c1.costs, c2.costs):
        if not isinstance(c1, SymbolicCost):
            continue
        print("-" * 10)
        print("comparing {} and {}".format(c1, c2))
        print("  c1 compare_to c2 = {}".format(c1.compare_to(c2, assumptions=assumptions)))
        print("  c2 compare_to c1 = {}".format(c2.compare_to(c1, assumptions=assumptions)))
        print("variable meanings...")
        for e, v in itertools.chain(c1.cardinalities.items(), c2.cardinalities.items()):
            print("  {v} = len {e}".format(v=pprint(v), e=pprint(e)))
        print("joint orderings...")
        cards = c1.order_cardinalities(c2, assumptions=assumptions)
        for o in break_conj(cards):
            print("  {}".format(pprint(o)))
        print("heuristics...")
        for h in itertools.chain(c1.heuristics, c2.heuristics):
            print("  {}".format(pprint(h)))
        for op in ("<=", "<", ">", ">="):
            print("c1 always {} c2?".format(op))
            x = []
            res = c1.always(op, c2, cards=cards, model_callback=lambda m: x.append(m))
            if res:
                print("  YES")
            elif not x:
                print("  NO (no model!?)")
            else:
                print("  NO: {}".format(x[0]))
                print("  c1 = {}".format(eval(c1.formula, env=x[0])))
                print("  c2 = {}".format(eval(c2.formula, env=x[0])))

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
    return build_balanced_tree(INT, "+", es)
