"""Static cost model to order expressions."""

from collections import OrderedDict
from enum import Enum

from cozy.common import OrderedSet
from cozy.target_syntax import *
from cozy.syntax_tools import pprint, fresh_var, free_vars, free_funcs, break_sum, all_exps, alpha_equivalent, mk_lambda
from cozy.contexts import Context
from cozy.typecheck import is_collection, is_numeric, is_scalar
from cozy.pools import Pool, RUNTIME_POOL, STATE_POOL
from cozy.solver import satisfy, ModelCachingSolver, valid
from cozy.evaluation import eval, eval_bulk
from cozy.structures import extension_handler
from cozy.logging import task, event
from cozy.state_maintenance import mutate

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

    def __init__(self, 
            assumptions     : Exp   = T, 
            examples                = (), 
            funcs                   = (), 
            freebies        : [Exp] = [], 
            ops             : [Op]  = []):
        self.solver = ModelCachingSolver(vars=(), funcs=funcs, examples=examples, assumptions=assumptions)
        self.assumptions = assumptions
        # self.examples = list(examples)
        self.funcs = OrderedDict(funcs)
        self.ops = ops
        self.freebies = freebies

    def __repr__(self):
        return "CostModel(assumptions={!r}, examples={!r}, funcs={!r}, freebies={!r}, ops={!r})".format(
            self.assumptions,
            self.examples,
            self.funcs,
            self.freebies,
            self.ops)

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
                    lambda: self._compare(
                        maintenance_cost(
                            e=e1, solver=self.solver, ops=self.ops, freebies=self.freebies),
                        maintenance_cost(
                            e=e2, solver=self.solver, ops=self.ops, freebies=self.freebies), context))
                    #lambda: self._compare(max_storage_size(e1, self.freebies), max_storage_size(e2, self.freebies), context),
                    #lambda: self._compare(rt(e1), rt(e2), context),
                    #lambda: order_objects(e1.size(), e2.size())) # index spec will be wrong if this line is uncommented
            else:
                return composite_order(
                    lambda: self._compare(
                        maintenance_cost(
                            e=e1, solver=self.solver, ops=self.ops, freebies=self.freebies),
                        maintenance_cost(
                            e=e2, solver=self.solver, ops=self.ops, freebies=self.freebies), context),
                    #lambda: self._compare(storage_size(e1, self.freebies), storage_size(e2, self.freebies), context),
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

def wc_card(e):
    assert is_collection(e.type)
    while isinstance(e, EFilter) or isinstance(e, EMap) or isinstance(e, EFlatMap) or isinstance(e, EMakeMap2) or isinstance(e, EStateVar) or (isinstance(e, EUnaryOp) and e.op == UOp.Distinct) or isinstance(e, EListSlice):
        e = e.e
    if isinstance(e, EBinOp) and e.op == "-":
        return wc_card(e.e1)
    if isinstance(e, EBinOp) and e.op == "+":
        return max(wc_card(e.e1), wc_card(e.e2))
    if isinstance(e, EFlatMap):
        return wc_card(e.e) * wc_card(e.f.body)
    if isinstance(e, ECond):
        return max(wc_card(e.then_branch), wc_card(e.else_branch))
    if isinstance(e, EEmptyList):
        return 0
    if isinstance(e, ESingleton):
        return 1
    return EXTREME_COST

def _maintenance_cost(e : Exp, solver : ModelCachingSolver, op : Op, freebies : [Exp] = []):
    e_prime = mutate(e, op.body)
#    print("e        : {}".format(pprint(e)))
#    print("e_prime  : {}".format(pprint(e_prime)))
    if solver.valid(EEq(e, e_prime)):
        return ZERO

    if is_scalar(e.type):
        return storage_size(e)
    elif isinstance(e.type, TBag) or isinstance(e.type, TSet):
        things_added = storage_size(
                EBinOp(e_prime, "-", e).with_type(e.type), freebies).with_type(INT)
        things_remov = storage_size(
                EBinOp(e, "-", e_prime).with_type(e.type), freebies).with_type(INT)

        return ESum([things_added, things_remov])
    elif isinstance(e.type, TList):
            return storage_size(e_prime, freebies)
    elif isinstance(e.type, TMap):
        keys = EMapKeys(e).with_type(TBag(e.type.k))
        vals = EMap(
            keys, 
            mk_lambda(
                e.type.k, 
                lambda k: EMapGet(e, k).with_type(e.type.v))).with_type(TBag(e.type.v))
        
        keys_prime = EMapKeys(e_prime).with_type(TBag(e_prime.type.k))
        vals_prime = EMap(
            keys_prime, 
            mk_lambda(
                e_prime.type.k, 
                lambda k: EMapGet(e_prime, k).with_type(e_prime.type.v))).with_type(TBag(e_prime.type.v))

        keys_added = storage_size(
            EBinOp(keys_prime, "-", keys).with_type(keys.type), freebies).with_type(INT) 
        keys_rmved = storage_size(
            EBinOp(keys, "-", keys_prime).with_type(keys.type), freebies).with_type(INT) 

        vals_added = storage_size(
            EBinOp(vals_prime, "-", vals).with_type(vals.type), freebies).with_type(INT) 
        vals_rmved = storage_size(
            EBinOp(vals, "-", vals_prime).with_type(vals.type), freebies).with_type(INT) 

        keys_difference = ESum([keys_added, keys_rmved])
        vals_difference = ESum([vals_added, vals_rmved])
        return EBinOp(keys_difference, "*", vals_difference).with_type(INT)

    else: 
        raise NotImplementedError(repr(e.type))

def maintenance_cost(e : Exp, solver : ModelCachingSolver, ops : [Op] = [], freebies : [Exp] = []):
    res = ZERO
#    for x in all_exps(e):
#        if isinstance(x, EStateVar):
#            print("e: {}".format(pprint(x.e)))
    for op in ops:
#        print(pprint(op))
        res = ESum([
            res,
            ESum([
                _maintenance_cost(
                    x.e, solver, op, freebies) for x in all_exps(e) if isinstance(x, EStateVar)])])
    return res


# These require walking over the entire collection.
# Some others (e.g. "exists" or "empty") just look at the first item.
LINEAR_TIME_UOPS = {
    UOp.Sum, UOp.Length,
    UOp.Distinct, UOp.AreUnique,
    UOp.All, UOp.Any,
    UOp.Reversed }

def asymptotic_runtime(e : Exp) -> int:
    res = 0
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
            res += max(wc_card(e.e) * asymptotic_runtime(e.p), asymptotic_runtime(e.e))
            continue
        if isinstance(e, EMap) or isinstance(e, EFlatMap) or isinstance(e, EArgMin) or isinstance(e, EArgMax):
            res += max(wc_card(e.e) * asymptotic_runtime(e.f), asymptotic_runtime(e.e))
            continue
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
    return max(res, 1)

def is_constant_time(e : Exp) -> bool:
    return asymptotic_runtime(e) < EXTREME_COST

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
    print("  res = {}".format(cm.compare(e1, e2, context=context, pool=RUNTIME_POOL)))
    print("-" * 20 + " {} ops...".format(len(cm.ops)))
    for o in cm.ops:
        print(pprint(o))
        for ename, e in [("e1", e1), ("e2", e2)]:
            print("maintenance_cost({e}) = {res}".format(e=ename, res=pprint(maintenance_cost(e, cm.solver, [o]))))

    print("-" * 20)
    for f in asymptotic_runtime, max_storage_size, rt:
        for ename, e in [("e1", e1), ("e2", e2)]:
            res = f(e)
            print("{f}({e}) = {res}".format(f=f.__name__, e=ename, res=(pprint(res) if isinstance(res, Exp) else res)))

    print("-" * 20 + " {} examples...".format(len(cm.examples)))
    for x in cm.examples:
        print(x)
        print("asympto(e1) = {}".format(asymptotic_runtime(e1)))
        print("asympto(e2) = {}".format(asymptotic_runtime(e2)))

        print("maintcost(e1) = {}".format(eval_bulk(maintenance_cost(e1, cm.solver, cm.ops), [x], use_default_values_for_undefined_vars=True)[0]))
        print("maintcost(e2) = {}".format(eval_bulk(maintenance_cost(e2, cm.solver, cm.ops), [x], use_default_values_for_undefined_vars=True)[0]))

        print("storage(e1) = {}".format(eval_bulk(max_storage_size(e1), [x], use_default_values_for_undefined_vars=True)[0]))
        print("storage(e2) = {}".format(eval_bulk(max_storage_size(e2), [x], use_default_values_for_undefined_vars=True)[0]))
        print("runtime(e1) = {}".format(eval_bulk(rt(e1), [x], use_default_values_for_undefined_vars=True)[0]))
        print("runtime(e2) = {}".format(eval_bulk(rt(e2), [x], use_default_values_for_undefined_vars=True)[0]))
        print("-" * 20)
