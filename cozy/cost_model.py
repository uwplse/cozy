from collections import OrderedDict
from functools import total_ordering, lru_cache, cmp_to_key
import itertools

import igraph

from cozy.common import OrderedSet, typechecked, partition, make_random_access, compare_with_lt, collapse_runs, product, exists, fresh_name
from cozy.target_syntax import *
from cozy.syntax_tools import BottomUpExplorer, pprint, equal, fresh_var, mk_lambda, free_vars, subst, alpha_equivalent, all_exps, ExpMap
from cozy.typecheck import is_collection
from cozy.pools import RUNTIME_POOL, STATE_POOL
from cozy.solver import valid, satisfiable, REAL, SolverReportedUnknown, IncrementalSolver
from cozy.evaluation import eval
from cozy.opts import Option

assume_large_cardinalities = Option("assume-large-cardinalities", int, 1000)
integer_cardinalities = Option("try-integer-cardinalities", bool, True)

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

class CardinalityLattice(object):
    """
    Maintains order amongst cardinalities of expressions.

    Notable properties:
        facts      - list of Exps expressing provable relations among cardinalities
        heuristics - list of Exps expressing probable relations among cardinalities
    """

    def __init__(self, assumptions : Exp = T):
        self.solver = IncrementalSolver() # for ordering lengths of collections
        self.ind1 = fresh_var(BOOL)
        self.ind2 = fresh_var(BOOL)
        self.solver.add_assumption(assumptions)
        self.cardinalities = OrderedDict() # Exp (in terms of collections) -> Exp (in terms of cards)
        self.cards_to_graph_verts = OrderedDict() # Maps cardinality exps to dag vertices
        self.graph_verts_to_cards = OrderedDict()
        self.dag = igraph.Graph().as_directed() # edges go smaller --> larger
        self.vars_seen = set()
        self.facts = []
        self.heuristics = []
        self.card_solver = IncrementalSolver(logic="QF_NIA") # for ordering expressions over cardinalities

    def add_fact(self, f : Exp):
        self.facts.append(f)
        self.card_solver.add_assumption(f)

    def add_heuristic(self, f : Exp):
        self.heuristics.append(f)
        self.card_solver.add_assumption(f)

    def cardinality(self, e : Exp) -> Exp:
        """
        Add `e` to the lattice and return an expression representing its cardinality
        """

        res = self.cardinalities.get(e)
        if res is not None:
            return res

        # print("{}.cardinality({})".format(id(self), pprint(e)))
        # if isinstance(e, EFilter):
        #     raise Exception()
        # for k in self.cardinalities:
        #     print(" --> " + pprint(k))

        assert is_collection(e.type)
        old = set(self.cardinalities.values())
        h = []
        res = cardinality(e, self.cardinalities, h)
        self.cardinalities[e] = res
        # print("|{}| = {}".format(pprint(e), pprint(res)))
        for f in h:
            self.add_heuristic(f)
        fresh = [item for item in self.cardinalities.values() if item not in old]
        rcards = { v : exp for (exp, v) in self.cardinalities.items() }

        g = self.dag
        s = self.solver

        for v1var in fresh:
            self.add_fact(EBinOp(v1var, ">=", ZERO).with_type(BOOL))
            v1 = fresh_name()
            g.add_vertex(name=v1)
            self.cards_to_graph_verts[v1var] = v1
            self.graph_verts_to_cards[v1] = v1var
            wq = OrderedSet(g.topological_sorting())
            while wq:
                vid = next(iter(wq))
                v2 = g.vs[vid]["name"]
                v2var = self.graph_verts_to_cards[v2]
                wq.remove(vid)
                if v1 == v2:
                    continue
                le = False
                ge = False
                ind_le = self.ind1
                ind_ge = self.ind2
                c1 = rcards[v1var]
                c2 = rcards[v2var]
                s.push()
                s.add_assumption(EAll([
                    EEq(ind_le, EBinOp(ELen(c1), "<=", ELen(c2)).with_type(BOOL)),
                    EEq(ind_ge, EBinOp(ELen(c2), "<=", ELen(c1)).with_type(BOOL))]))

                if s.valid(ind_le):
                    g.add_edge(v1, v2)
                    for vv in g.subcomponent(vid, mode="OUT"): # will include vid as well
                        try:
                            wq.remove(vv)
                        except KeyError:
                            pass
                    le = True
                if s.valid(ind_ge):
                    g.add_edge(v2, v1)
                    ge = True
                s.pop()
                if le and not ge:
                    self.add_fact(EBinOp(v1var, "<=", v2var).with_type(BOOL))
                elif ge and not le:
                    self.add_fact(EBinOp(v1var, ">=", v2var).with_type(BOOL))
                elif le and ge:
                    # union
                    # print("union {} and {}".format(v1, v2))
                    self.add_fact(EEq(v1var, v2var))
                    g.delete_vertices([v1])
                    self.cards_to_graph_verts[v1var] = v2
                    self.graph_verts_to_cards[v1] = v2var
                    break

        if assume_large_cardinalities.value > 0:
            min_cardinality = ENum(assume_large_cardinalities.value).with_type(INT)
            for v in free_vars(e):
                if is_collection(v.type) and v not in self.vars_seen:
                    c = self.cardinality(v)
                    self.add_heuristic(EGt(c, min_cardinality))
                    self.vars_seen.add(v)

        # if not s.satisfiable(EAll(self.facts + self.heuristics)):
        #     print("FACTS")
        #     for f in self.facts:
        #         print("  {}".format(pprint(f)))
        #     print("HEURISTICS")
        #     for f in self.heuristics:
        #         print("  {}".format(pprint(f)))
        #     assert False

        return res

    def cardinality_lt(self, v1 : EVar, v2 : EVar):
        v1 = self.cards_to_graph_verts[v1]
        v2 = self.cards_to_graph_verts[v2]
        if v1 == v2:
            return False
        # Ugh igraph you're killllllllling meeee... why no convenience methods?
        # This method returns an array A where A[i][j] gives the shortest path
        # length from source[i] to target[j], or +infinity if no path exists.
        path_len = self.dag.shortest_paths(source=[v1], target=[v2])[0][0]
        return path_len != float("inf")

    def order_expressions_over_cardinalities(self, f1 : Exp, f2 : Exp):
        if isinstance(f1, ENum) and isinstance(f2, ENum):
            if f1.val < f2.val:
                return Cost.BETTER
            elif f1.val == f2.val:
                return Cost.UNORDERED
            else:
                return Cost.WORSE

        s = self.card_solver
        s.push()
        s.add_assumption(EAll([
            EEq(self.ind1, EBinOp(f1, "<=", f2).with_type(BOOL)),
            EEq(self.ind2, EBinOp(f2, "<=", f1).with_type(BOOL))]))
        try:
            o1 = s.valid(self.ind1)
            o2 = s.valid(self.ind2)
        except SolverReportedUnknown:
            print("WARNING: gave up on cost comparison")
            return Cost.UNORDERED
        finally:
            s.pop()
        if o1 and not o2:
            return Cost.BETTER
        elif o2 and not o1:
            return Cost.WORSE
        else:
            return Cost.UNORDERED

class Factor(object):
    def __init__(self, lattice : CardinalityLattice, e : Exp):
        assert isinstance(e, EVar) or isinstance(e, ENum), pprint(e)
        self.lattice = lattice
        self.e = e
    def __lt__(self, other):
        assert isinstance(other, Factor)
        if isinstance(self.e, ENum) and isinstance(other.e, EVar):
            return True
        elif isinstance(self.e, ENum) and isinstance(other.e, ENum):
            return self.e.val < other.e.val
        elif isinstance(self.e, EVar) and isinstance(other.e, EVar):
            return self.lattice.cardinality_lt(self.e, other.e)
        assert isinstance(self.e, EVar) and isinstance(other.e, ENum)
        return False
    def __str__(self):
        return pprint(self.e)

class Term(object):
    def __init__(self, factors : [Factor], constant : int = 1):
        factors = sorted(factors,
            reverse=True,
            key=cmp_to_key(compare_with_lt))
        constants, factors = partition(factors, lambda f: isinstance(f.e, ENum))
        self.constant = constant * product(c.e.val for c in constants)
        self.factors = factors
    def __lt__(self, other):
        """
        Goals:
            x < 2*x
            x < x*y
            z < x*y
            a*b < c*d if a<=b, c<=d, and a<=c
        """
        assert isinstance(other, Term)
        v1 = self.factors
        v2 = other.factors
        if len(v1) < len(v2): return True
        if len(v2) < len(v1): return False
        for x1, x2 in zip(v1, v2):
            # print("comparing {}, {}".format(x1, x2))
            if x1 < x2:
                # print("  <")
                return True
            if x2 < x1:
                # print("  >")
                return False
            # print("  ~")
        return self.constant < other.constant
    def __str__(self):
        return "*".join(str(f) for f in self.factors)

def find_match(xs, ys, p):
    for x in xs:
        for y in ys:
            if p(x, y):
                return (x, y)
    return None

class Polynomial(object):
    def __init__(self, terms : [Term]):
        self.terms = sorted(terms,
            reverse=True,
            key=cmp_to_key(compare_with_lt))
    def __lt__(self, other):
        """
        Excluding terms we have in common,
          does the other have a term such that all my terms are smaller?
        """
        assert isinstance(other, Polynomial)
        p1 = list(self.terms)
        p2 = list(other.terms)
        while True:
            m = find_match(p1, p2, lambda x, y: not (x<y or y<x))
            if m is None:
                break
            p1.remove(m[0])
            p2.remove(m[1])
        return exists(p2,
            lambda a: all(b < a for b in p1))
    def __str__(self):
        return " + ".join(str(f) for f in self.terms)

def nf(f : Exp, lattice : CardinalityLattice) -> Polynomial:
    from cozy.syntax_tools import BottomUpRewriter
    def mul(e1, e2):
        return EBinOp(e1, "*", e2).with_type(e1.type)
    class V(BottomUpRewriter):
        def visit_EBinOp(self, e):
            l = self.visit(e.e1)
            r = self.visit(e.e2)
            if e.op == "*":
                if isinstance(l, ENum) and isinstance(r, ENum):
                    return ENum(l.val * r.val).with_type(l.type)
                if isinstance(l, EBinOp) and l.op == "+":
                    return self.visit(EBinOp(mul(l.e1, r), "+", mul(l.e2, r)).with_type(e.type))
                if isinstance(r, EBinOp) and r.op == "+":
                    return self.visit(EBinOp(mul(l, r.e1), "+", mul(l, r.e2)).with_type(e.type))
            if e.op == "+":
                if isinstance(l, ENum) and isinstance(r, ENum):
                    return ENum(l.val + r.val).with_type(l.type)
                if l == ZERO:
                    return r
                if r == ZERO:
                    return l
            return EBinOp(l, e.op, r).with_type(e.type)

    f = V().visit(f)
    return Polynomial(
        Term(Factor(lattice, factor)
            for factor in break_product(term))
        for term in break_sum(f))

class SymbolicCost(Cost):
    @typechecked
    def __init__(self, formula : Exp, lattice : CardinalityLattice):
        self._formula = formula
        if True or isinstance(formula, EVar) or isinstance(formula, ENum):
            self.formula = formula
        else:
            self.formula = fresh_var(INT)
            lattice.add_fact(EEq(self.formula, formula))
        self.lattice = lattice
        self._nf = nf(formula, lattice)
        # print(formula)
        # print(self._nf)
    def __repr__(self):
        return "SymbolicCost({!r}, {!r})".format(self._formula, self.lattice)
    def __str__(self):
        # return pprint(self._formula)
        return str(self._nf)
    def compare_to(self, other, assumptions : Exp = T, solver : IncrementalSolver = None):
        assert isinstance(other, SymbolicCost)
        assert other.lattice is self.lattice
        if self._nf < other._nf:
            assert not (other._nf < self._nf), "{} vs {}".format(self, other)
            return Cost.BETTER
        elif other._nf < self._nf:
            return Cost.WORSE
        else:
            return Cost.UNORDERED
        return self.lattice.order_expressions_over_cardinalities(self.formula, other.formula)

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
    def __init__(self, assumptions : Exp = T):
        self.lattice = CardinalityLattice(assumptions=assumptions)
    def __repr__(self):
        return "CompositeCostModel()"
    def is_monotonic(self):
        return False
    def cardinality(self, e : Exp) -> Polynomial:
        assert is_collection(e.type)
        return nf(self.lattice.cardinality(e), self.lattice)
    def cost(self, e, pool):
        if pool == STATE_POOL:
            return CompositeCost(
                sizeof(e, self.lattice),
                ast_size(e))
        else:
            assert pool == RUNTIME_POOL
            return CompositeCost(
                asymptotic_runtime(e, self.lattice),
                storage_size(e, self.lattice),
                precise_runtime(e, self.lattice),
                ast_size(e))

def maybe_inline(e, f):
    if isinstance(e, ENum) or isinstance(e, EVar):
        return f(e)
    v = fresh_var(e.type, omit=free_vars(f(T)))
    body = f(v)
    return ELet(e, ELambda(v, body)).with_type(body.type)

def _ECond(x, y, z):
    if isinstance(x, EBool):
        return y if x.val else z
    return ECond(x, y, z).with_type(y.type)

def _EGt(x, y):
    if isinstance(x, ENum) and isinstance(y, ENum):
        return T if x.val > y.val else F
    return EGt(x, y)

def EMax(es):
    return ESum(es)
    es = make_random_access(es)
    assert es
    assert all(isinstance(e, Exp) for e in es), es
    res = es[0]
    t = res.type
    fvs = set(v.id for v in free_vars(res))
    for i in range(1, len(es)):
        res = maybe_inline(res,   lambda v1:
              maybe_inline(es[i], lambda v2:
                _ECond(_EGt(v1, v2), v1, v2)))
    return res

def asymptotic_runtime(e, lattice):
    def _EMax(es):
        return max(es, key=lambda e: nf(e, lattice))
    class V(BottomUpExplorer):
        def EBinOp(self, e1, op, e2):
            if isinstance(e1, list): e1 = _EMax([ONE] + e1)
            if isinstance(e2, list): e2 = _EMax([ONE] + e2)
            if op == "*":
                if e1 == ENum(1): return e2
                if e2 == ENum(1): return e1
            e = EBinOp(e1, op, e2).with_type(e1.type)
            if isinstance(e1, ENum) and isinstance(e2, ENum):
                return ENum(eval(e, {})).with_type(e1.type)
            return e
        def cardinality(self, e : Exp, **kwargs) -> Exp:
            return lattice.cardinality(e)
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
            # return _EMax([ONE] + res)
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
                costs.append(EBinOp(
                    self.cardinality(e.e1), "*",
                    self.cardinality(e.e2)).with_type(INT))
            return self.combine(costs)
        def visit_ELambda(self, e):
            # avoid name collisions with fresh_var
            # return self.visit(e.apply_to(fresh_var(e.arg.type))) # NO NO: breaks caching!
            return self.visit(e.body)
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
    f = _EMax([ONE] + vis.visit(e))
    # f = cse(f)
    return SymbolicCost(f, lattice)

def sizeof(e, lattice):
    terms = [ONE]
    if is_collection(e.type):
        terms.append(lattice.cardinality(e))
    elif isinstance(e.type, TMap):
        ks = EMapKeys(e).with_type(TBag(e.type.k))
        terms.append(lattice.cardinality(ks))
        if is_collection(e.type.v):
            vals = EFlatMap(ks, mk_lambda(e.type.k, lambda k: EMapGet(e, k).with_type(e.type.v))).with_type(e.type.v)
            terms.append(lattice.cardinality(vals))
    return SymbolicCost(ESum(terms), lattice)

def storage_size(e, lattice):
    sizes = []
    for x in all_exps(e):
        if isinstance(x, EStateVar):
            sz_cost = sizeof(x.e, lattice)
            sizes.append(sz_cost.formula)
    return SymbolicCost(ESum(sizes), lattice)

# Some kinds of expressions have a massive penalty associated with them if they
# appear at runtime.
EXTREME_COST    = ENum(1000).with_type(INT)
MILD_PENALTY    = ENum(  10).with_type(INT)
TWO             = ENum(   2).with_type(INT)

def precise_runtime(e, lattice):
    class V(BottomUpExplorer):
        def __init__(self):
            super().__init__()
            self.cardinalities = { }
        def cardinality(self, e : Exp, **kwargs) -> Exp:
            return lattice.cardinality(e)
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
            # return self.visit(e.apply_to(fresh_var(e.arg.type)))
            return self.visit(e.body)
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
    return SymbolicCost(f, lattice)

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
        # if isinstance(e, EFilter):
        #     cc = cardinality(e.e, cache, heuristics)
        #     # heuristics.append(EBinOp(v, "<=", cc).with_type(BOOL))
        #     # heuristic: (xs) large implies (filter_p xs) large
        #     heuristics.append(EBinOp(
        #         EBinOp(v,  "*", ENum(5).with_type(INT)).with_type(INT), ">=",
        #         EBinOp(cc, "*", ENum(4).with_type(INT)).with_type(INT)).with_type(BOOL))
        if isinstance(e, EUnaryOp) and e.op == UOp.Distinct:
            cc = cardinality(e.e, cache, heuristics)
            # heuristics.append(EBinOp(v, "<=", cc).with_type(BOOL))
            # heuristics.append(EImplies(EGt(cc, ZERO), EGt(v, ZERO)))
            # heuristic: (xs) large implies (distinct xs) large
            # heuristics.append(EBinOp(
            #     EBinOp(v,  "*", ENum(5).with_type(INT)).with_type(INT), ">=",
            #     EBinOp(cc, "*", ENum(4).with_type(INT)).with_type(INT)).with_type(BOOL))
            heuristics.append(EImplies(EGt(cc, ZERO), EGt(v, ZERO)))
        # if isinstance(e, EBinOp) and e.op == "-":
        #     heuristics.append(EBinOp(v, "<=", cardinality(e.e1, cache, heuristics)).with_type(BOOL))
        # if isinstance(e, ECond):
        #     heuristics.append(EAny([EEq(v, cardinality(e.then_branch, cache, heuristics)), EEq(v, self.cardinality(e.else_branch))]))
        return v

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
        cmp = c1.compare_to(c2, assumptions=assumptions)
        print("  c1 compare_to c2 = {}".format(cmp))
        print("  c2 compare_to c1 = {}".format(c2.compare_to(c1, assumptions=assumptions)))
        print("variable meanings...")
        for e, v in c1.lattice.cardinalities.items():
            print("  {v} = len {e}".format(v=pprint(v), e=pprint(e)))
        print("proven facts...")
        for o in c1.lattice.facts:
            print("  {}".format(pprint(o)))
        print("heuristics...")
        for o in c1.lattice.heuristics:
            print("  {}".format(pprint(o)))
        if cmp != Cost.UNORDERED:
            break

def break_sum(e):
    if isinstance(e, EBinOp) and e.op == "+":
        yield from break_sum(e.e1)
        yield from break_sum(e.e2)
    else:
        yield e

def break_product(e):
    if isinstance(e, EBinOp) and e.op == "*":
        yield from break_product(e.e1)
        yield from break_product(e.e2)
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
