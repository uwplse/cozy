from collections import namedtuple, OrderedDict
import itertools

from cozy.common import pick_to_sum, OrderedSet, FrozenDict
from cozy.target_syntax import *
from cozy.syntax_tools import pprint, fresh_var, all_exps, strip_EStateVar
from cozy.evaluation import eval_bulk
from cozy.synthesis.cache import Cache, SeenSet
from cozy.typecheck import is_numeric, is_scalar
from cozy.cost_model import CostModel, Cost
from cozy.pools import Pool, ALL_POOLS, RUNTIME_POOL, STATE_POOL, pool_name
from cozy.opts import Option

use_cost_ceiling = Option("cost-ceiling", bool, True)
hyperaggressive_eviction = Option("hyperaggressive-eviction", bool, False)

def fingerprint(e : Exp, examples : [{str:object}]):
    return (e.type,) + tuple(eval_bulk(e, examples))

EnumeratedExp = namedtuple("EnumeratedExp", [
    "e",                # The expression
    "pool",             # The pool it lives in
    "size",             # Its size
    "fingerprint",      # Its fingerprint
    "cost",             # Its cost
    "replaced",         # The expression it was better than [might be None]
    "replaced_size",    # The size of the replaced expression [might be None]
    "replaced_cost",    # The cost of the replaced expression [might be None]
    ])

LITERALS = [(e, pool)
    for e in (T, F, ZERO, ONE)
    for pool in ALL_POOLS]

oracle = EBinOp(
    ESingleton(EGetField(EVar('x').with_type(THandle('H', TInt())), 'val')), '-',
    EUnaryOp('distinct', EMap(EBinOp(EStateVar(EVar('xs').with_type(TBag(THandle('H', TInt())))), '-', ESingleton(EVar('x').with_type(THandle('H', TInt())))), ELambda(EVar('_var4').with_type(THandle('H', TInt())), EGetField(EVar('_var4').with_type(THandle('H', TInt())), 'val')))))
def _interesting(depth : int, e : Exp, pool : Pool):
    from cozy.syntax_tools import alpha_equivalent
    if depth > 0:
        return False
    return oracle is not None and any(alpha_equivalent(e, x) for x in all_exps(oracle))
    # return hasattr(e, "_tag")
    # return False
    # return depth == 0 # and (isinstance(e, EMakeMap2) or isinstance(e, EMapGet))

def _on_consider(depth : int, e : Exp, pool : Pool):
    if _interesting(depth, e, pool):
        print(" > considering {} in {}".format(pprint(e), pool_name(pool)))

def _on_skip(depth : int, e : Exp, pool : Pool, reason : str, **data):
    if _interesting(depth, e, pool):
        print("   > skipping {}; {}; {}".format(pprint(e), reason, data))
        # if "ceiling" in reason:
        #     raise Exception()

def _on_evict(depth : int, e : Exp, pool : Pool, better_alternative : Exp, better_cost : Cost):
    if _interesting(depth, e, pool):
        print("   > evicting {}; {}".format(pprint(e), pprint(better_alternative)))

def _on_accept(depth : int, e : Exp, pool : Pool):
    if _interesting(depth, e, pool):
        print("   > accepting {} in {} : {}".format(pprint(e), pool_name(pool), pprint(e.type)))

def build_candidates(cache : Cache, size : int, scopes : {EVar:Exp}, build_lambdas):
    for pool in ALL_POOLS:

        for e in cache.find(pool=pool, size=size-1):
            t = TBag(e.type)
            yield (EEmptyList().with_type(t), pool)
            yield (ESingleton(e).with_type(t), pool)

        for e in cache.find(pool=pool, type=TRecord, size=size-1):
            for (f,t) in e.type.fields:
                yield (EGetField(e, f).with_type(t), pool)
        for e in cache.find_collections(pool=pool, size=size-1):
            if is_numeric(e.type.t):
                yield (EUnaryOp(UOp.Sum, e).with_type(e.type.t), pool)
        for e in cache.find(pool=pool, type=THandle, size=size-1):
            yield (EGetField(e, "val").with_type(e.type.value_type), pool)
        for e in cache.find(pool=pool, type=TTuple, size=size-1):
            for n in range(len(e.type.ts)):
                yield (ETupleGet(e, n).with_type(e.type.ts[n]), pool)
        for e in cache.find(pool=pool, type=BOOL, size=size-1):
            yield (EUnaryOp(UOp.Not, e).with_type(BOOL), pool)
        for e in cache.find(pool=pool, type=INT, size=size-1):
            yield (EUnaryOp("-", e).with_type(INT), pool)

        for m in cache.find(pool=pool, type=TMap, size=size-1):
            yield (EMapKeys(m).with_type(TBag(m.type.k)), pool)

        for (sz1, sz2) in pick_to_sum(2, size - 1):
            for a1 in cache.find(pool=pool, size=sz1):
                if not is_numeric(a1.type):
                    continue
                for a2 in cache.find(pool=pool, type=a1.type, size=sz2):
                    yield (EBinOp(a1, "+", a2).with_type(INT), pool)
                    yield (EBinOp(a1, "-", a2).with_type(INT), pool)
                    yield (EBinOp(a1, ">", a2).with_type(BOOL), pool)
                    yield (EBinOp(a1, "<", a2).with_type(BOOL), pool)
                    yield (EBinOp(a1, ">=", a2).with_type(BOOL), pool)
                    yield (EBinOp(a1, "<=", a2).with_type(BOOL), pool)
            for a1 in cache.find_collections(pool=pool, size=sz1):
                for a2 in cache.find(pool=pool, type=a1.type, size=sz2):
                    yield (EBinOp(a1, "+", a2).with_type(a1.type), pool)
                    yield (EBinOp(a1, "-", a2).with_type(a1.type), pool)
                for a2 in cache.find(pool=pool, type=a1.type.t, size=sz2):
                    yield (EBinOp(a2, BOp.In, a1).with_type(BOOL), pool)
            for a1 in cache.find(pool=pool, type=BOOL, size=sz1):
                for a2 in cache.find(pool=pool, type=BOOL, size=sz2):
                    yield (EBinOp(a1, BOp.And, a2).with_type(BOOL), pool)
                    yield (EBinOp(a1, BOp.Or, a2).with_type(BOOL), pool)
            for a1 in cache.find(pool=pool, size=sz1):
                if not isinstance(a1.type, TMap):
                    for a2 in cache.find(pool=pool, type=a1.type, size=sz2):
                        yield (EEq(a1, a2), pool)
                        yield (EBinOp(a1, "!=", a2).with_type(BOOL), pool)
            for m in cache.find(pool=pool, type=TMap, size=sz1):
                for k in cache.find(pool=pool, type=m.type.k, size=sz2):
                    yield (EMapGet(m, k).with_type(m.type.v), pool)
                    yield (EHasKey(m, k).with_type(BOOL), pool)

        for (sz1, sz2, sz3) in pick_to_sum(3, size-1):
            for cond in cache.find(pool=pool, type=BOOL, size=sz1):
                for then_branch in cache.find(pool=pool, size=sz2):
                    for else_branch in cache.find(pool=pool, size=sz3, type=then_branch.type):
                        yield (ECond(cond, then_branch, else_branch).with_type(then_branch.type), pool)

        for bag in cache.find_collections(pool=pool, size=size-1):
            # len of bag
            count = EUnaryOp(UOp.Length, bag).with_type(INT)
            yield (count, pool)
            # empty?
            yield (EUnaryOp(UOp.Empty, bag).with_type(BOOL), pool)
            # exists?
            yield (EUnaryOp(UOp.Exists, bag).with_type(BOOL), pool)
            # singleton?
            yield (EEq(count, ONE), pool)

            yield (EUnaryOp(UOp.The, bag).with_type(bag.type.t), pool)
            yield (EUnaryOp(UOp.Distinct, bag).with_type(bag.type), pool)
            yield (EUnaryOp(UOp.AreUnique, bag).with_type(BOOL), pool)

            if bag.type.t == BOOL:
                yield (EUnaryOp(UOp.Any, bag).with_type(BOOL), pool)
                yield (EUnaryOp(UOp.All, bag).with_type(BOOL), pool)

        # Iteration
        for (sz1, sz2) in pick_to_sum(2, size - 1):
            for bag in cache.find_collections(pool=pool, size=sz1):
                for lam in build_lambdas(bag, pool, sz2):
                    body_type = lam.body.type
                    yield (EMap(bag, lam).with_type(TBag(body_type)), pool)
                    if body_type == BOOL:
                        yield (EFilter(bag, lam).with_type(bag.type), pool)
                    if is_numeric(body_type):
                        yield (EArgMin(bag, lam).with_type(bag.type.t), pool)
                        yield (EArgMax(bag, lam).with_type(bag.type.t), pool)
                    if isinstance(body_type, TBag):
                        yield (EFlatMap(bag, lam).with_type(TBag(body_type.t)), pool)

    # Enable use of a state-pool expression at runtime
    for e in cache.find(pool=STATE_POOL, size=size-1):
        yield (EStateVar(e).with_type(e.type), RUNTIME_POOL)

    # Convert a runtime expression to state-pool form
    for e in cache.find(pool=RUNTIME_POOL, size=size-1):
        if isinstance(e, EStateVar):
            continue
        e = strip_EStateVar(e)
        yield (e, STATE_POOL)
        yield (EStateVar(e).with_type(e.type), RUNTIME_POOL)

    # Create maps
    for (sz1, sz2) in pick_to_sum(2, size - 1):
        for bag in cache.find_collections(pool=STATE_POOL, size=sz1):
            if not is_scalar(bag.type.t):
                continue
            for lam in build_lambdas(bag, STATE_POOL, sz2):
                t = TMap(bag.type.t, lam.body.type)
                m = EMakeMap2(bag, lam).with_type(t)
                yield (m, STATE_POOL)

class MemoizedBuilder(object):
    __slots__ = ("cache", "iter")
    def __init__(self, *args, **kwargs):
        self.cache = []
        self.iter = enumerate_exps(*args, **kwargs)
    def get(self, size):
        if size < 0:
            return ()
        if size >= len(self.cache):
            for res in self.iter:
                while len(self.cache) <= res.size:
                    self.cache.append([])
                self.cache[res.size].append(res)
                if res.size > size:
                    break
        return self.cache[size]

def enumerate_exps(
        roots        : [(Exp, Pool)],
        examples     : [{str:object}],
        cost_model   : CostModel,
        cost_ceiling : Cost = None,
        size_ceiling : int = None,
        check_wf = None,
        build_candidates = build_candidates,
        scopes : {EVar:Exp} = None):

    """
    Enumerate expressions in order of size, starting with the given roots (and
    some literals) at size zero.  Expressions are deduplicated; an expression
    is only yielded if it is
        (1) new (it behaves differently on at least one example from every
            other expression yielded so far) or
        (2) better (it behaves identically to some other expression, but has
            lower cost)

    Yields EnumeratedExp objects.
    """

    if scopes is None:
        scopes = {}
    depth = len(scopes)
    cache = Cache()
    seen = SeenSet()
    size = 0

    lbuilders = { }

    def build_lambdas(bag, pool, size):
        bag = strip_EStateVar(bag)
        tup = lbuilders.get(bag)
        if tup is None:
            v = fresh_var(bag.type.t)
            # TODO: inform the cost model about v's relationship to other
            # variables, i.e. EDeepIn(v, bag)
            new_roots = roots + [(v, pool)]
            new_examples = OrderedSet()
            for (e, b) in zip(examples, eval_bulk(bag, examples)):
                e = dict(e)
                for x in b:
                    e[v.id] = x
                    new_examples.add(FrozenDict(e))
            new_examples = list(new_examples)
            new_scopes = OrderedDict(scopes)
            new_scopes[v] = bag
            builder = MemoizedBuilder(
                new_roots,
                new_examples,
                cost_model,
                cost_ceiling,
                size_ceiling=None,
                check_wf=check_wf,
                build_candidates=build_candidates,
                scopes=new_scopes)
            lbuilders[bag] = (v, builder)
        else:
            v, builder = tup
        for res in builder.get(size):
            if res.pool == pool:
                yield ELambda(v, res.e)

    while size_ceiling is None or size <= size_ceiling:
        it = build_candidates(cache, size, scopes, build_lambdas)
        if size == 0:
            it = itertools.chain(roots, LITERALS, it)
        for e, pool in it:
            _on_consider(depth, e, pool)
            if check_wf is not None and not check_wf(e, pool):
                _on_skip(depth, e, pool, "not well-formed")
                continue

            cost = cost_model.cost(e, pool)
            if pool == RUNTIME_POOL and use_cost_ceiling.value and cost_ceiling is not None and cost.compare_to(cost_ceiling) == Cost.WORSE:
                _on_skip(depth, e, pool, "worse than cost ceiling")
                # if _interesting(depth, e, pool):
                #     print(cost)
                #     print(cost_ceiling)
                #     from cozy.cost_model import debug_comparison
                #     debug_comparison(e, cost, EVar("target"), cost_ceiling)
                #     print(repr(e))
                continue

            fp = fingerprint(e, examples)
            prev = list(seen.find_all(pool, fp))

            should_add = True
            better_than = None
            worse_than = None
            for prev_exp, prev_size, prev_cost in prev:
                ordering = cost.compare_to(prev_cost)
                if ordering == Cost.UNORDERED:
                    _on_skip(depth, e, pool, "equivalent to", other=prev_exp, other_cost=prev_cost)
                    should_add = False
                    break
                elif ordering == Cost.BETTER:
                    better_than = (prev_exp, prev_size, prev_cost)
                    to_evict = []
                    if hyperaggressive_eviction.value:
                        for (cached_e, size, p) in list(cache):
                            if p != pool:
                                continue
                            if prev_exp in all_exps(cached_e):
                                to_evict.append((cached_e, size))
                    else:
                        to_evict.append((prev_exp, prev_size))
                    for evict_e, evict_size in to_evict:
                        _on_evict(depth, evict_e, pool, better_alternative=e, better_cost=cost)
                        cache.evict(evict_e, size=evict_size, pool=pool)
                        seen.remove(evict_e, pool, fp)
                else:
                    should_add = False
                    worse_than = (prev_exp, prev_size, prev_cost)
                    _on_skip(depth, e, pool, "worse than", other=prev_exp, other_cost=prev_cost)
                    break

            if should_add:
                _on_accept(depth, e, pool)
                cache.add(e, pool=pool, size=size)
                seen.add(e, pool, fp, size, cost)
                yield EnumeratedExp(
                    e             = e,
                    pool          = pool,
                    size          = size,
                    fingerprint   = fp,
                    cost          = cost,
                    replaced      = better_than[0] if better_than is not None else None,
                    replaced_size = better_than[1] if better_than is not None else None,
                    replaced_cost = better_than[2] if better_than is not None else None)

        if not depth:
            print("|cache|={}".format(len(cache)))
        size += 1
