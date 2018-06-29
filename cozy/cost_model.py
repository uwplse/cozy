"""Static cost model to order expressions."""

from collections import OrderedDict
from enum import Enum
import functools

from cozy.common import OrderedSet
from cozy.target_syntax import *
from cozy.syntax_tools import pprint, fresh_var, free_vars, free_funcs, all_exps, alpha_equivalent
from cozy.contexts import Context
from cozy.typecheck import is_collection, is_numeric
from cozy.pools import Pool, RUNTIME_POOL
from cozy.solver import ModelCachingSolver
from cozy.evaluation import eval, eval_bulk
from cozy.structures import extension_handler
from cozy.logging import task, event

class Order(Enum):
    EQUAL     = 0
    LT        = 1
    GT        = 2
    AMBIGUOUS = 3

def composite_order(*funcs):
    for f in funcs:
        o = f()
        if o != Order.EQUAL:
            return o
    return Order.EQUAL

def order_objects(x, y):
    if x < y: return Order.LT
    if y < x: return Order.GT
    return Order.EQUAL

class CostModel(object):

    def __init__(self, assumptions : Exp = T, examples=(), funcs=(), freebies : [Exp] = []):
        self.solver = ModelCachingSolver(vars=(), funcs=funcs, examples=examples, assumptions=assumptions)
        self.assumptions = assumptions
        # self.examples = list(examples)
        self.funcs = OrderedDict(funcs)
        self.freebies = freebies

    def __repr__(self):
        return "CostModel(assumptions={!r}, examples={!r}, funcs={!r}, freebies={!r})".format(
            self.assumptions,
            self.examples,
            self.funcs,
            self.freebies)

    @property
    def examples(self):
        return tuple(self.solver.examples)

    def _compare(self, e1 : Exp, e2 : Exp, context : Context):
        e1_constant = not free_vars(e1) and not free_funcs(e1)
        e2_constant = not free_vars(e2) and not free_funcs(e2)
        if e1_constant and e2_constant:
            e1v = eval(e1, {})
            e2v = eval(e2, {})
            event("comparison obvious on constants: {} vs {}".format(e1v, e2v))
            return order_objects(e1v, e2v)
        if alpha_equivalent(e1, e2):
            event("shortcutting comparison of identical terms")
            return Order.EQUAL

        path_condition = EAll(context.path_conditions())
        always_le = self.solver.valid(EImplies(path_condition, ELe(e1, e2)))
        always_ge = self.solver.valid(EImplies(path_condition, EGe(e1, e2)))

        if always_le and always_ge:
            return Order.EQUAL
        if always_le:
            return Order.LT
        if always_ge:
            return Order.GT
        return Order.AMBIGUOUS

    def compare(self, e1 : Exp, e2 : Exp, context : Context, pool : Pool) -> Order:
        with task("compare costs", context=context):
            if pool == RUNTIME_POOL:
                return composite_order(
                    lambda: order_objects(asymptotic_runtime(e1), asymptotic_runtime(e2)),
                    lambda: self._compare(max_storage_size(e1, self.freebies), max_storage_size(e2, self.freebies), context),
                    lambda: self._compare(rt(e1), rt(e2), context),
                    lambda: order_objects(e1.size(), e2.size()))
            else:
                return composite_order(
                    lambda: self._compare(storage_size(e1, self.freebies), storage_size(e2, self.freebies), context),
                    lambda: order_objects(e1.size(), e2.size()))

def card(e):
    assert is_collection(e.type)
    return ELen(e)

TWO   = ENum(2).with_type(INT)
FOUR  = ENum(4).with_type(INT)
EIGHT = ENum(8).with_type(INT)
TWENTY = ENum(20).with_type(INT)
def storage_size(e, freebies : [Exp] = []):
    h = extension_handler(type(e.type))
    if h is not None:
        return h.storage_size(e, k=storage_size)

    if e in freebies:
        return ZERO
    elif e.type == BOOL:
        return ONE
    elif is_numeric(e.type) or isinstance(e.type, THandle):
        return FOUR
    elif isinstance(e.type, TEnum):
        return TWO
    elif isinstance(e.type, TNative):
        return FOUR
    elif isinstance(e.type, TString):
        return TWENTY
    elif isinstance(e.type, TTuple):
        return ESum([storage_size(ETupleGet(e, n).with_type(t)) for (n, t) in enumerate(e.type.ts)])
    elif isinstance(e.type, TRecord):
        return ESum([storage_size(EGetField(e, f).with_type(t)) for (f, t) in e.type.fields])
    elif is_collection(e.type):
        v = fresh_var(e.type.t, omit=free_vars(e))
        return ESum([
            FOUR,
            EUnaryOp(UOp.Sum, EMap(e, ELambda(v, storage_size(v))).with_type(INT_BAG)).with_type(INT)])
    elif isinstance(e.type, TMap):
        k = fresh_var(e.type.k, omit=free_vars(e))
        return ESum([
            FOUR,
            EUnaryOp(UOp.Sum, EMap(
                EMapKeys(e).with_type(TBag(e.type.k)),
                ELambda(k, ESum([
                    storage_size(k),
                    storage_size(EMapGet(e, k).with_type(e.type.v))]))).with_type(INT_BAG)).with_type(INT)])
    else:
        raise NotImplementedError(e.type)

def max_storage_size(e, freebies : [Exp] = []):
    sizes = OrderedSet()
    for x in all_exps(e):
        if isinstance(x, EStateVar):
            sizes.add(storage_size(x.e, freebies))
    return max_of(*sizes, type=INT)

def hash_cost(e):
    return storage_size(e)

def comparison_cost(e1, e2):
    return ESum([storage_size(e1), storage_size(e2)])

def wc_card(e : Exp) -> DominantTerm:
    assert is_collection(e.type)
    while isinstance(e, EFilter) or isinstance(e, EMap) or isinstance(e, EFlatMap) or isinstance(e, EMakeMap2) or isinstance(e, EStateVar) or (isinstance(e, EUnaryOp) and e.op == UOp.Distinct) or isinstance(e, EListSlice):
        e = e.e
    if isinstance(e, EBinOp) and e.op == "-":
        return wc_card(e.e1)
    if isinstance(e, EBinOp) and e.op == "+":
        return wc_card(e.e1) + wc_card(e.e2)
    if isinstance(e, EFlatMap):
        return wc_card(e.e) * wc_card(e.f.body)
    if isinstance(e, ECond):
        return max(wc_card(e.then_branch), wc_card(e.else_branch))
    if isinstance(e, EEmptyList):
        return DominantTerm.ZERO
    if isinstance(e, ESingleton):
        return DominantTerm.ONE
    return DominantTerm.N

# These require walking over the entire collection.
# Some others (e.g. "exists" or "empty") just look at the first item.
LINEAR_TIME_UOPS = {
    UOp.Sum, UOp.Length,
    UOp.Distinct, UOp.AreUnique,
    UOp.All, UOp.Any,
    UOp.Reversed }

@functools.total_ordering
class DominantTerm(object):
    """A term of the form c*n^e for some unknown n.

    Instances of this class can be added, multiplied, and compared.  A term
    with a higher exponent is always greater than one with a lower exponent.
    """
    __slots__ = ("multiplier", "exponent")
    def __init__(self, multiplier, exponent):
        self.multiplier = multiplier
        self.exponent = exponent
    def __eq__(self, other):
        return self.multiplier == other.multiplier and self.exponent == other.exponent
    def __lt__(self, other):
        return (self.exponent, self.multiplier) < (other.exponent, other.multiplier)
    def __str__(self):
        return "{}n^{}".format(self.multiplier, self.exponent)
    def __repr__(self):
        return "DominantTerm({}, {})".format(self.multiplier, self.exponent)
    def __add__(self, other):
        if other.exponent == self.exponent:
            return DominantTerm(self.multiplier + other.multiplier, self.exponent)
        if other.exponent > self.exponent:
            return other
        return self
    def __mul__(self, other):
        return DominantTerm(self.multiplier * other.multiplier, self.exponent + other.exponent)

DominantTerm.ZERO = DominantTerm(0, 0)
DominantTerm.ONE  = DominantTerm(1, 0)
DominantTerm.N    = DominantTerm(1, 1)

def asymptotic_runtime(e : Exp) -> DominantTerm:
    res = DominantTerm.ZERO
    stk = [e]
    while stk:
        e = stk.pop()
        if isinstance(e, tuple) or isinstance(e, list):
            stk.extend(e)
            continue
        if not isinstance(e, Exp):
            continue
        if isinstance(e, ELambda):
            e = e.body
        if isinstance(e, EFilter):
            res += wc_card(e.e) * asymptotic_runtime(e.p) + asymptotic_runtime(e.e)
            continue
        if isinstance(e, EMap) or isinstance(e, EFlatMap) or isinstance(e, EArgMin) or isinstance(e, EArgMax):
            res += wc_card(e.e) * asymptotic_runtime(e.f) + asymptotic_runtime(e.e)
            continue
        res += DominantTerm.ONE
        if isinstance(e, EMakeMap2):
            res += wc_card(e.e) * asymptotic_runtime(e.value)
        if isinstance(e, EBinOp) and e.op == BOp.In:
            res += wc_card(e.e2)
        if isinstance(e, EBinOp) and e.op == "-" and is_collection(e.type):
            res += wc_card(e.e1) + wc_card(e.e2) + wc_card(e.e1) * wc_card(e.e2)
        if isinstance(e, EUnaryOp) and e.op in LINEAR_TIME_UOPS:
            res += wc_card(e.e)
        if isinstance(e, ECond):
            res += max(asymptotic_runtime(e.then_branch), asymptotic_runtime(e.else_branch))
            stk.append(e.cond)
            continue
        if isinstance(e, EStateVar):
            continue
        stk.extend(e.children())
    if res.exponent == 0:
        return DominantTerm.ONE
    return res

def is_constant_time(e : Exp) -> bool:
    return asymptotic_runtime(e).exponent == 0

# Some kinds of expressions have a massive penalty associated with them if they
# appear at runtime.
EXTREME_COST = 1000
def rt(e, account_for_constant_factors=True):
    constant = 0
    terms = []
    stk = [e]
    while stk:
        e = stk.pop()
        if isinstance(e, tuple) or isinstance(e, list):
            stk.extend(e)
            continue
        if isinstance(e, str) or isinstance(e, int):
            continue
        if isinstance(e, ELambda):
            continue
        if isinstance(e, EBinOp) and e.op == BOp.In:
            v = fresh_var(e.e1.type, omit=free_vars(e.e1))
            stk.append(e.e1)
            stk.append(EUnaryOp(UOp.Any, EMap(e.e2, ELambda(v, EEq(v, e.e1))).with_type(BOOL_BAG)).with_type(BOOL))
            continue
        if isinstance(e, EBinOp) and e.op == BOp.And:
            stk.append(e.e1)
            terms.append(ECond(e.e1, rt(e.e2), ZERO).with_type(INT))
            continue
        if isinstance(e, EBinOp) and e.op == BOp.Or:
            stk.append(e.e1)
            terms.append(ECond(e.e1, ZERO, rt(e.e2)).with_type(INT))
            continue
        if isinstance(e, ECond):
            stk.append(e.cond)
            terms.append(ECond(e.cond,
                rt(e.then_branch),
                rt(e.else_branch)).with_type(INT))
            continue

        constant += 1
        if isinstance(e, EStateVar):
            continue
        if isinstance(e, Exp):
            stk.extend(e.children())

        if isinstance(e, EFilter):
            # constant += EXTREME_COST
            terms.append(EUnaryOp(UOp.Sum, EMap(e.e, ELambda(e.p.arg, rt(e.p.body))).with_type(INT_BAG)).with_type(INT))
        elif isinstance(e, EMap) or isinstance(e, EFlatMap) or isinstance(e, EArgMin) or isinstance(e, EArgMax):
            # constant += EXTREME_COST
            terms.append(EUnaryOp(UOp.Sum, EMap(e.e, ELambda(e.f.arg, rt(e.f.body))).with_type(INT_BAG)).with_type(INT))
        elif isinstance(e, EListSlice):
            terms.append(max_of(ZERO, EBinOp(e.end, "-", e.start).with_type(INT)))
        elif isinstance(e, EMakeMap2):
            constant += EXTREME_COST
            terms.append(EUnaryOp(UOp.Sum, EMap(e.e, ELambda(e.value.arg, rt(e.value.body))).with_type(INT_BAG)).with_type(INT))
        elif isinstance(e, EBinOp) and e.op == "-" and is_collection(e.type):
            constant += EXTREME_COST
            terms.append(card(e.e1))
            terms.append(card(e.e2))
        elif isinstance(e, EBinOp) and e.op in ("==", "!=", ">", "<", ">=", "<="):
            terms.append(comparison_cost(e.e1, e.e2))
        elif isinstance(e, EUnaryOp) and e.op in LINEAR_TIME_UOPS:
            terms.append(card(e.e))
        elif isinstance(e, EMapGet):
            terms.append(hash_cost(e.key))
            terms.append(comparison_cost(e.key, e.key))

    terms.append(ENum(constant).with_type(INT))
    if not account_for_constant_factors:
        terms = [t for t in terms if not isinstance(t, ENum)]
    return ESum(terms)

def debug_comparison(cm : CostModel, e1 : Exp, e2 : Exp, context : Context):
    """Print information about the cost relationship of two expressions.

    This procedure gives a lot of insight into the relationship between e1 and
    e2 under the given cost model.
    """

    print("-" * 20)
    print("Comparing")
    print("  e1 = {}".format(pprint(e1)))
    print("  e2 = {}".format(pprint(e2)))
    print("-" * 20 + " {} examples...".format(len(cm.examples)))
    for f in asymptotic_runtime, max_storage_size, rt:
        for ename, e in [("e1", e1), ("e2", e2)]:
            print("{f}({e}) = {res}".format(f=f.__name__, e=ename, res=pprint(f(e))))
    for x in cm.examples:
        print("-" * 20)
        print(x)
        print("asympto(e1) = {}".format(asymptotic_runtime(e1)))
        print("asympto(e2) = {}".format(asymptotic_runtime(e2)))
        print("storage(e1) = {}".format(eval_bulk(max_storage_size(e1), [x], use_default_values_for_undefined_vars=True)[0]))
        print("storage(e2) = {}".format(eval_bulk(max_storage_size(e2), [x], use_default_values_for_undefined_vars=True)[0]))
        print("runtime(e1) = {}".format(eval_bulk(rt(e1), [x], use_default_values_for_undefined_vars=True)[0]))
        print("runtime(e2) = {}".format(eval_bulk(rt(e2), [x], use_default_values_for_undefined_vars=True)[0]))
    print("-" * 20)
