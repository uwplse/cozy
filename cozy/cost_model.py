"""Static cost model to order expressions."""

from collections import OrderedDict
from enum import Enum

from cozy.common import OrderedSet
from cozy.target_syntax import *
from cozy.syntax_tools import pprint, fresh_var, free_vars, free_funcs, all_exps, alpha_equivalent, mk_lambda, map_value_func
from cozy.contexts import Context
from cozy.typecheck import is_collection, is_numeric, is_scalar
from cozy.pools import Pool, RUNTIME_POOL
from cozy.solver import ModelCachingSolver
from cozy.evaluation import eval, eval_bulk
from cozy.structures import extension_handler
from cozy.logging import task, event
from cozy.state_maintenance import mutate
from cozy.polynomials import Polynomial, DominantTerm
from cozy.opts import Option
from cozy.structures.treemultiset import ETreeMultisetElems, ETreeMultisetPeek

cost_model_selection = Option("cost-model", int, 2,
    description="Cost model to use.  "
        + "Higher numbers are much slower to evaluate but often yield better results.  "
        + "0: optimize for expression size.  "
        + "1: optimize for asymptotic runtime.  "
        + "2: optimize for a mix of asymptotic runtime, storage size, and exact runtime.  "
        + "3: optimize for a mix of asymptotic runtime and state maintenance cost.")

class Order(Enum):
    EQUAL     = "="
    LT        = "<"
    GT        = ">"
    AMBIGUOUS = "?"

    def flip(order):
        """Flips the direction of the Order.

        Less than becomes greater than (and vice versa).  Equals and ambiguous
        are unchanged.
        """
        if order == Order.LT:
            return Order.GT
        if order == Order.GT:
            return Order.LT
        return order

    def could_be(self, order):
        """Returns true if this is the given order or AMBIGUOUS."""
        return self in (order, Order.AMBIGUOUS)

def prioritized_order(*funcs):
    """Combine several Orders where you know which ones are more important.

    Each argument should be a function that takes no arguments and returns an
    Order.

    Returns the first result that is not Order.EQUAL from calling each func in
    sequence.

    This procedure is useful when
     - you have several metrics to compare and you know which ones are most
       important
     - the metrics are very difficult to compute so you do not want to compute
       them unless you are certain you need them
    """
    for f in funcs:
        o = f()
        if o != Order.EQUAL:
            return o
    return Order.EQUAL

def unprioritized_order(*funcs):
    """Combine several Orders where it is unclear which are more important.

    Each argument should be a function that takes no argument and returns an
    Order.

    This function behaves according to these rules:
     - if any input is ambiguous, the result is ambiguous
     - if both > and < are present, the result is ambiguous
     - if only one of > or < is present, the result is that order
     - otherwise all inputs are equal and the result is equal

    This procedure is useful when
     - you have several metrics to compare and you do NOT know which ones are
       most important
     - the metrics are very difficult to compute so you do not want to compute
       them unless you are certain you need them
    """
    # This set should only be 1 big
    orders_seen = set()
    for f in funcs:
        op = f()
        if op == Order.EQUAL:        # Ignores equals
            continue
        # Immediately returns ambiguous, change to `continue` if want to ignore
        if op == Order.AMBIGUOUS:
            return Order.AMBIGUOUS
        # Check if we've seen both < and >
        if op.flip() in orders_seen:
            return Order.AMBIGUOUS
        orders_seen.add(op)

    return orders_seen.pop() if orders_seen else Order.EQUAL

def order_objects(x, y) -> Order:
    """Compare x and y as regular Python objects and return an Order.

    Note: this function never returns Order.AMBIGUOUS."""
    if x < y: return Order.LT
    if y < x: return Order.GT
    return Order.EQUAL

class CostModel(object):

    def __init__(self,
            assumptions     : Exp   = ETRUE,
            examples                = (),
            funcs                   = (),
            freebies        : [Exp] = [],
            ops             : [Op]  = []):
        """
        assumptions : assumed to be true when comparing expressions
        examples    : initial examples (the right set of examples can speed up
                      some cost comparisons; it is always safe to leave this
                      set empty)
        funcs       : in-scope functions
        freebies    : state variables that can be used for free
        ops         : mutators which are used to determine how expensive it is
                      to maintain a state variable
        """
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
            selection = cost_model_selection.value
            if selection == 0:
                return order_objects(e1.size(), e2.size())
            if selection == 1:
                if pool == RUNTIME_POOL:
                    return prioritized_order(
                        lambda: order_objects(polynomial_runtime(e1), polynomial_runtime(e2)),
                        lambda: order_objects(e1.size(), e2.size()))
                else:
                    return order_objects(e1.size(), e2.size())
            if selection == 2:
                if pool == RUNTIME_POOL:
                    return prioritized_order(
                        lambda: order_objects(asymptotic_runtime(e1), asymptotic_runtime(e2)),
                        lambda: self._compare(max_storage_size(e1, self.freebies), max_storage_size(e2, self.freebies), context),
                        lambda: self._compare(rt(e1), rt(e2), context),
                        lambda: order_objects(e1.size(), e2.size()))
                else:
                    return prioritized_order(
                        lambda: self._compare(storage_size(e1, self.freebies), storage_size(e2, self.freebies), context),
                        lambda: order_objects(e1.size(), e2.size()))
            if selection == 3:
                if pool == RUNTIME_POOL:
                    return prioritized_order(
                        lambda: order_objects(asymptotic_runtime(e1), asymptotic_runtime(e2)),
                        lambda: unprioritized_order(
                            lambda: prioritized_order(
                                lambda: self._compare(
                                    max_storage_size(e1, self.freebies),
                                    max_storage_size(e2, self.freebies), context),
                                lambda: self._compare(rt(e1), rt(e2), context)),
                            *[lambda op=op: self._compare(
                                maintenance_cost(e1, op, self.freebies),
                                maintenance_cost(e2, op, self.freebies),
                                context) for op in self.ops]),
                        lambda: order_objects(e1.size(), e2.size()))
                else:
                    return prioritized_order(
                        lambda: self._compare(storage_size(e1, self.freebies), storage_size(e2, self.freebies), context),
                        lambda: order_objects(e1.size(), e2.size()))
            raise ValueError("illegal value for --{}: {}".format(cost_model_selection.name, selection))

def cardinality(e : Exp) -> Exp:
    assert is_collection(e.type)
    return ELen(e)

TWO   = ENum(2).with_type(INT)
FOUR  = ENum(4).with_type(INT)
EIGHT = ENum(8).with_type(INT)
TWENTY = ENum(20).with_type(INT)
def storage_size(e, freebies : [Exp] = []):
    h = extension_handler(type(e.type))
    if h is not None:
        return h.storage_size(e, storage_size=storage_size)

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
        v = fresh_var(e.type.elem_type, omit=free_vars(e))
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

def worst_case_cardinality(e : Exp) -> Polynomial:
    assert is_collection(e.type)
    while isinstance(e, EFilter) or isinstance(e, EMap) or isinstance(e, EFlatMap) or isinstance(e, EMakeMap2) or isinstance(e, EStateVar) or (isinstance(e, EUnaryOp) and e.op == UOp.Distinct) or isinstance(e, EListSlice):
        e = e.e
    if isinstance(e, EBinOp) and e.op == "-":
        return worst_case_cardinality(e.e1)
    if isinstance(e, EBinOp) and e.op == "+":
        return worst_case_cardinality(e.e1) + worst_case_cardinality(e.e2)
    if isinstance(e, EFlatMap):
        return worst_case_cardinality(e.e) * worst_case_cardinality(e.transform_function.body)
    if isinstance(e, ECond):
        return max(worst_case_cardinality(e.then_branch), worst_case_cardinality(e.else_branch))
    if isinstance(e, EEmptyList):
        return Polynomial.ZERO
    if isinstance(e, ESingleton):
        return Polynomial.ONE
    if isinstance(e, EMapGet):
        try:
            return worst_case_cardinality(map_value_func(e.map).body)
        except NotImplementedError:
            print("WARNING: unable to peer inside map {}".format(pprint(e.map)))
            return Polynomial.N
    return Polynomial.N

def _maintenance_cost(e : Exp, op : Op, freebies : [Exp] = []):
    """Determines the cost of maintaining the expression when there are
    freebies and ops being considered.

    The cost is the result of mutating the expression and getting the storage
    size of the difference between the mutated expression and the original.
    """
    e_prime = mutate(e, op.body)
    if alpha_equivalent(e, e_prime):
        return ZERO

    h = extension_handler(type(e.type))
    if h is not None:
        return h.maintenance_cost(
            old_value=e,
            new_value=e_prime,
            op=op,
            freebies=freebies,
            storage_size=storage_size,
            maintenance_cost=_maintenance_cost)

    if is_scalar(e.type):
        return storage_size(e, freebies)
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

def maintenance_cost(e : Exp, op : Op, freebies : [Exp] = []):
    """This method calulates the result over all expressions that are EStateVar """
    return ESum([_maintenance_cost(e=x.e, op=op, freebies=freebies) for x in all_exps(e) if isinstance(x, EStateVar)])

# These require walking over the entire collection.
# Some others (e.g. "exists" or "empty") just look at the first item.
LINEAR_TIME_UOPS = {
    UOp.Sum, UOp.Length,
    UOp.Distinct, UOp.AreUnique,
    UOp.All, UOp.Any,
    UOp.Reversed }

def polynomial_runtime(e : Exp) -> Polynomial:
    res = Polynomial.ZERO
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
            stk.append(e.e)
            res += worst_case_cardinality(e.e) * polynomial_runtime(e.predicate)
            continue
        if isinstance(e, EArgMin) or isinstance(e, EArgMax):
            stk.append(e.e)
            res += worst_case_cardinality(e.e) * polynomial_runtime(e.key_function)
            continue
        if isinstance(e, ESorted):
            stk.append(e.e)
            n = worst_case_cardinality(e.e)
            res += n * n
            continue
        if isinstance(e, EMap) or isinstance(e, EFlatMap):
            stk.append(e.e)
            res += worst_case_cardinality(e.e) * polynomial_runtime(e.transform_function)
            continue
        if isinstance(e, ELet):
            stk.append(e.e)
            stk.append(e.body_function.body)
            continue
        res += Polynomial.ONE
        if isinstance(e, EMakeMap2):
            res += worst_case_cardinality(e.e) * polynomial_runtime(e.value_function)
        if isinstance(e, EBinOp) and e.op == BOp.In:
            res += worst_case_cardinality(e.e2)
        if isinstance(e, EBinOp) and e.op == "-" and is_collection(e.type):
            res += worst_case_cardinality(e.e1) + worst_case_cardinality(e.e2) + worst_case_cardinality(e.e1) * worst_case_cardinality(e.e2)
        if isinstance(e, EUnaryOp) and e.op in LINEAR_TIME_UOPS:
            res += worst_case_cardinality(e.e)
        if isinstance(e, ECond):
            res += max(polynomial_runtime(e.then_branch), polynomial_runtime(e.else_branch))
            stk.append(e.cond)
            continue
        if isinstance(e, EStateVar):
            continue
        stk.extend(e.children())
    return res

def asymptotic_runtime(e : Exp) -> DominantTerm:
    res = polynomial_runtime(e).largest_term()
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
        if isinstance(e, ELet):
            stk.append(e.e)
            terms.append(ELet(e.e, ELambda(e.body_function.arg, rt(e.body_function.body))).with_type(INT))
            continue
        if isinstance(e, ETreeMultisetPeek):
            stk.append(e.index)
            continue
        if isinstance(e, EListGet) and isinstance(e.e, ETreeMultisetElems):
            constant += 1
            stk.append(e.index)
            continue
        constant += 1
        if isinstance(e, EStateVar):
            continue
        if isinstance(e, Exp):
            stk.extend(e.children())

        if isinstance(e, EFilter):
            # constant += EXTREME_COST
            terms.append(EUnaryOp(UOp.Sum, EMap(e.e, ELambda(e.predicate.arg, rt(e.predicate.body))).with_type(INT_BAG)).with_type(INT))
        elif isinstance(e, EArgMin) or isinstance(e, EArgMax):
            # constant += EXTREME_COST
            terms.append(EUnaryOp(UOp.Sum, EMap(e.e, ELambda(e.key_function.arg, rt(e.key_function.body))).with_type(INT_BAG)).with_type(INT))
        elif isinstance(e, EMap) or isinstance(e, EFlatMap):
            terms.append(EUnaryOp(UOp.Sum, EMap(e.e, ELambda(e.transform_function.arg, rt(e.transform_function.body))).with_type(INT_BAG)).with_type(INT))
        elif isinstance(e, EListSlice):
            terms.append(max_of(ZERO, EBinOp(e.end, "-", e.start).with_type(INT)))
        elif isinstance(e, EMakeMap2):
            constant += EXTREME_COST
            terms.append(EUnaryOp(UOp.Sum, EMap(e.e, ELambda(e.value_function.arg, rt(e.value_function.body))).with_type(INT_BAG)).with_type(INT))
        elif isinstance(e, EBinOp) and e.op == "-" and is_collection(e.type):
            constant += EXTREME_COST
            terms.append(cardinality(e.e1))
            terms.append(cardinality(e.e2))
        elif isinstance(e, EBinOp) and e.op in ("==", "!=", ">", "<", ">=", "<="):
            terms.append(comparison_cost(e.e1, e.e2))
        elif isinstance(e, EUnaryOp) and e.op in LINEAR_TIME_UOPS:
            terms.append(cardinality(e.e))
        elif isinstance(e, EMapGet):
            terms.append(hash_cost(e.key))
            terms.append(comparison_cost(e.key, e.key))
        elif isinstance(e, ETreeMultisetElems):
            terms.append(cardinality(e))

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
    if is_collection(e1.type):
        print("worst_case_cardinality(e1) = {}".format(worst_case_cardinality(e1)))
    if is_collection(e2.type):
        print("worst_case_cardinality(e2) = {}".format(worst_case_cardinality(e2)))
    print("-" * 20 + " {} freebies...".format(len(cm.freebies)))
    for freebie in cm.freebies:
        print("  * {}".format(pprint(freebie)))
    print("-" * 20 + " {} ops...".format(len(cm.ops)))
    for o in cm.ops:
        print(pprint(o))
        for ename, e in [("e1", e1), ("e2", e2)]:
            print("maintenance_cost({e}) = {res}".format(e=ename, res=pprint(maintenance_cost(e, o))))

    print("-" * 20)
    for f in asymptotic_runtime, polynomial_runtime, max_storage_size, rt:
        for ename, e in [("e1", e1), ("e2", e2)]:
            res = f(e)
            print("{f}({e}) = {res}".format(f=f.__name__, e=ename, res=(pprint(res) if isinstance(res, Exp) else res)))

    print("-" * 20 + " {} examples...".format(len(cm.examples)))
    for x in cm.examples:
        print(x)

        for op in cm.ops:
            print(pprint(op))
            print("maintcost(e1) = {}".format(eval_bulk(maintenance_cost(e1, op), [x], use_default_values_for_undefined_vars=True)[0]))
            print("maintcost(e2) = {}".format(eval_bulk(maintenance_cost(e2, op), [x], use_default_values_for_undefined_vars=True)[0]))

        print("storage(e1) = {}".format(eval_bulk(max_storage_size(e1), [x], use_default_values_for_undefined_vars=True)[0]))
        print("storage(e2) = {}".format(eval_bulk(max_storage_size(e2), [x], use_default_values_for_undefined_vars=True)[0]))
        print("runtime(e1) = {}".format(eval_bulk(rt(e1), [x], use_default_values_for_undefined_vars=True)[0]))
        print("runtime(e2) = {}".format(eval_bulk(rt(e2), [x], use_default_values_for_undefined_vars=True)[0]))
        print("-" * 20)
