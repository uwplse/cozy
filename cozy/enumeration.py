from collections import namedtuple, OrderedDict
from enum import Enum
import itertools

from cozy.common import pick_to_sum, OrderedSet, unique, make_random_access, StopException
from cozy.target_syntax import *
from cozy.syntax_tools import pprint, fresh_var, free_vars, freshen_binders
from cozy.evaluation import eval_bulk
from cozy.typecheck import is_numeric, is_scalar, is_collection
from cozy.cost_model import CostModel, Order
from cozy.pools import Pool, ALL_POOLS, RUNTIME_POOL, STATE_POOL, pool_name
from cozy.contexts import Context, RootCtx, UnderBinder
from cozy.logging import task, task_begin, task_end, event, verbose

def fingerprint(e : Exp, examples : [{str:object}]):
    return (e.type,) + tuple(eval_bulk(e, examples))

EnumeratedExp = namedtuple("EnumeratedExp", [
    "e",                # The expression
    "fingerprint",      # Its fingerprint
    "cost",             # Its cost
    ])

LITERALS = [(e, pool)
    for e in (T, F, ZERO, ONE)
    for pool in ALL_POOLS]

def of_type(exps, t):
    for e in exps:
        if e.type == t:
            yield e

def collections(exps):
    for e in exps:
        if is_collection(e.type):
            yield e

def most_general_context_for(context, fvs):
    assert context.legal_for(fvs), "{} does not belong in {}".format(fvs, context)
    parent = context.parent()
    while (parent is not None) and (parent.legal_for(fvs)):
        context = parent
        parent = context.parent()
    return context

def belongs_in_context(fvs, context):
    return context is most_general_context_for(context, fvs)

def parent_contexts(context):
    while context:
        parent = context.parent()
        yield parent
        context = parent

def _interesting(e, context):
    return isinstance(context, RootCtx) and hasattr(e, "_tag")
    # return True
def _consider(e, context):
    if _interesting(e, context) and not verbose.value:
        print("considering {} in {}".format(pprint(e), context))
    task_begin("considering {} in {}".format(pprint(e), context))
def _accept(e, context):
    if _interesting(e, context) and not verbose.value:
        print("accepting")
    event("accepting")
    task_end()
def _skip(e, context, reason):
    if _interesting(e, context) and not verbose.value:
        print("skipping [{}]".format(reason))
    event("skipping [{}]".format(reason))
    task_end()
def _evict(e, context, better_exp):
    if _interesting(e, context) and not verbose.value:
        print("evicting {}".format(pprint(e)))
    event("evicting {}".format(pprint(e)))

class Enumerator(object):
    def __init__(self, examples, cost_model : CostModel, check_wf=None, hints=None, heuristics=None, stop_callback=None):
        self.examples = list(examples)
        self.cost_model = cost_model
        self.cache = { } # keys -> [exp]
        self.seen = { }  # (ctx, pool, fp) -> frontier, i.e. [exp]
        self.in_progress = set()
        if check_wf is None:
            check_wf = lambda e, ctx, pool: True
        self.check_wf = check_wf
        self.hints = list(hints)
        if heuristics is None:
            heuristics = lambda e, ctx, pool: ()
        self.heuristics = heuristics
        if stop_callback is None:
            stop_callback = lambda: False
        self.stop_callback = stop_callback

    def cache_size(self):
        return sum(len(v) for v in self.cache.values())

    def enumerate_core(self, context : Context, size : int, pool : Pool) -> [Exp]:
        """
        Arguments:
            conext : a Context object describing the vars in scope
            size   : size to enumerate
            pool   : pool to enumerate

        Yields all expressions of the given size legal in the given context and
        pool.
        """

        if size < 0:
            return

        if size == 0:
            for (e, p) in LITERALS:
                if p == pool:
                    yield e
            for (v, p) in context.vars():
                if p == pool:
                    yield v
            for (e, ctx, p) in self.hints:
                if p == pool and ctx.alpha_equivalent(context):
                    yield context.adapt(e, ctx)
            return

        for e in collections(self.enumerate(context, size-1, pool)):
            yield EEmptyList().with_type(e.type)
            if is_numeric(e.type.t):
                yield EUnaryOp(UOp.Sum, e).with_type(e.type.t)

        for e in self.enumerate(context, size-1, pool):
            yield ESingleton(e).with_type(TBag(e.type))

        for e in self.enumerate(context, size-1, pool):
            if isinstance(e.type, TRecord):
                for (f,t) in e.type.fields:
                    yield EGetField(e, f).with_type(t)

        for e in self.enumerate(context, size-1, pool):
            if isinstance(e.type, THandle):
                yield EGetField(e, "val").with_type(e.type.value_type)

        for e in self.enumerate(context, size-1, pool):
            if isinstance(e.type, TTuple):
                for n in range(len(e.type.ts)):
                    yield ETupleGet(e, n).with_type(e.type.ts[n])

        for e in of_type(self.enumerate(context, size-1, pool), BOOL):
            yield EUnaryOp(UOp.Not, e).with_type(BOOL)

        for e in self.enumerate(context, size-1, pool):
            if is_numeric(e.type):
                yield EUnaryOp("-", e).with_type(INT)

        for m in self.enumerate(context, size-1, pool):
            if isinstance(m.type, TMap):
                yield EMapKeys(m).with_type(TBag(m.type.k))

        for (sz1, sz2) in pick_to_sum(2, size - 1):
            for a1 in self.enumerate(context, sz1, pool):
                t = a1.type
                if not is_numeric(t):
                    continue
                for a2 in of_type(self.enumerate(context, sz2, pool), t):
                    yield EBinOp(a1, "+", a2).with_type(t)
                    yield EBinOp(a1, "-", a2).with_type(t)
                    yield EBinOp(a1, ">", a2).with_type(BOOL)
                    yield EBinOp(a1, "<", a2).with_type(BOOL)
                    yield EBinOp(a1, ">=", a2).with_type(BOOL)
                    yield EBinOp(a1, "<=", a2).with_type(BOOL)
            for a1 in collections(self.enumerate(context, sz1, pool)):
                for a2 in of_type(self.enumerate(context, sz2, pool), a1.type):
                    yield EBinOp(a1, "+", a2).with_type(a1.type)
                    yield EBinOp(a1, "-", a2).with_type(a1.type)
                for a2 in of_type(self.enumerate(context, sz2, pool), a1.type.t):
                    yield EBinOp(a2, BOp.In, a1).with_type(BOOL)
            for a1 in of_type(self.enumerate(context, sz1, pool), BOOL):
                for a2 in of_type(self.enumerate(context, sz2, pool), BOOL):
                    yield EBinOp(a1, BOp.And, a2).with_type(BOOL)
                    yield EBinOp(a1, BOp.Or, a2).with_type(BOOL)
            for a1 in self.enumerate(context, sz1, pool):
                if not isinstance(a1.type, TMap):
                    for a2 in of_type(self.enumerate(context, sz2, pool), a1.type):
                        yield EEq(a1, a2)
                        yield EBinOp(a1, "!=", a2).with_type(BOOL)
            for m in self.enumerate(context, sz1, pool):
                if isinstance(m.type, TMap):
                    for k in of_type(self.enumerate(context, sz2, pool), m.type.k):
                        yield EMapGet(m, k).with_type(m.type.v)
                        yield EHasKey(m, k).with_type(BOOL)

        for (sz1, sz2, sz3) in pick_to_sum(3, size-1):
            for cond in of_type(self.enumerate(context, sz1, pool), BOOL):
                for then_branch in self.enumerate(context, sz2, pool):
                    for else_branch in of_type(self.enumerate(context, sz2, pool), then_branch.type):
                        yield ECond(cond, then_branch, else_branch).with_type(then_branch.type)

        for bag in collections(self.enumerate(context, size-1, pool)):
            # len of bag
            count = EUnaryOp(UOp.Length, bag).with_type(INT)
            yield count
            # empty?
            yield EUnaryOp(UOp.Empty, bag).with_type(BOOL)
            # exists?
            yield EUnaryOp(UOp.Exists, bag).with_type(BOOL)
            # singleton?
            yield EEq(count, ONE)

            yield EUnaryOp(UOp.The, bag).with_type(bag.type.t)
            yield EUnaryOp(UOp.Distinct, bag).with_type(bag.type)
            yield EUnaryOp(UOp.AreUnique, bag).with_type(BOOL)

            if bag.type.t == BOOL:
                yield EUnaryOp(UOp.Any, bag).with_type(BOOL)
                yield EUnaryOp(UOp.All, bag).with_type(BOOL)

        def build_lambdas(bag, pool, body_size):
            v = fresh_var(bag.type.t, omit=set(v for v, p in context.vars()))
            inner_context = UnderBinder(context, v=v, bag=bag, bag_pool=pool)
            for lam_body in self.enumerate(inner_context, body_size, pool):
                yield ELambda(v, lam_body)

        # Iteration
        for (sz1, sz2) in pick_to_sum(2, size - 1):
            for bag in collections(self.enumerate(context, sz1, pool)):
                for lam in build_lambdas(bag, pool, sz2):
                    body_type = lam.body.type
                    yield EMap(bag, lam).with_type(TBag(body_type))
                    if body_type == BOOL:
                        yield EFilter(bag, lam).with_type(bag.type)
                    if is_numeric(body_type):
                        yield EArgMin(bag, lam).with_type(bag.type.t)
                        yield EArgMax(bag, lam).with_type(bag.type.t)
                    if is_collection(body_type):
                        yield EFlatMap(bag, lam).with_type(TBag(body_type.t))

        # Enable use of a state-pool expression at runtime
        if pool == RUNTIME_POOL:
            for e in self.enumerate(context, size-1, STATE_POOL):
                yield EStateVar(e).with_type(e.type)

        # Create maps
        if pool == STATE_POOL:
            for (sz1, sz2) in pick_to_sum(2, size - 1):
                for bag in collections(self.enumerate(context, sz1, STATE_POOL)):
                    if not is_scalar(bag.type.t):
                        continue
                    for lam in build_lambdas(bag, STATE_POOL, sz2):
                        t = TMap(bag.type.t, lam.body.type)
                        m = EMakeMap2(bag, lam).with_type(t)
                        yield m

    def enumerate(self, context : Context, size : int, pool : Pool) -> [Exp]:
        for info in self.enumerate_with_info(context, size, pool):
            yield info.e

    def known_contexts(self):
        return unique(ctx for (ctx, pool, fp) in self.seen.keys())

    def canonical_context(self, context):
        # TODO: deduplicate based on examples, not alpha equivalence
        for ctx in self.known_contexts():
            if ctx != context and ctx.alpha_equivalent(context):
                return ctx
        return context

    def enumerate_with_info(self, context : Context, size : int, pool : Pool) -> [EnumeratedExp]:
        canonical_context = self.canonical_context(context)
        if canonical_context is not context:
            print("adapting request: {} ---> {}".format(context, canonical_context))
            for info in self.enumerate_with_info(canonical_context, size, pool):
                yield info._replace(e=context.adapt(info.e, canonical_context))
            return

        if context.parent() is not None:
            yield from self.enumerate_with_info(context.parent(), size, pool)

        k = (pool, size, context)
        res = self.cache.get(k)
        if res is not None:
            # print("[[{} cached @ size={}]]".format(len(res), size))
            for e in res:
                yield e
        else:
            # print("ENTER {}".format(k))
            examples = context.instantiate_examples(self.examples)
            assert k not in self.in_progress, "recursive enumeration?? {}".format(k)
            self.in_progress.add(k)
            res = []
            self.cache[k] = res
            queue = self.enumerate_core(context, size, pool)
            cost_model = self.cost_model
            while True:
                if self.stop_callback():
                    raise StopException()

                try:
                    e = next(queue)
                except StopIteration:
                    break

                fvs = free_vars(e)
                if not belongs_in_context(fvs, context):
                    continue

                e = freshen_binders(e, context)
                _consider(e, context)

                wf = self.check_wf(e, context, pool)
                if not wf:
                    _skip(e, context, "wf={}".format(wf))
                    continue

                fp = fingerprint(e, examples)

                # collect all expressions from parent contexts
                prev = []
                for ctx in itertools.chain([context], parent_contexts(context)):
                    for prev_exp in self.seen.get((ctx, pool, fp), ()):
                        prev.append((ctx, prev_exp))

                # decide whether to keep this expression,
                # decide which can be evicted
                should_keep = True
                # cost = self.cost_model.cost(e, pool)
                # print("prev={}".format(prev))
                # print("seen={}".format(self.seen))
                for ctx, prev_exp in prev:
                    # prev_cost = self.cost_model.cost(prev_exp, pool)
                    # ordering = cost.compare_to(prev_cost)
                    ordering = cost_model.compare(e, prev_exp, context, pool)
                    if ordering == Order.LT:
                        pass
                    elif ordering == Order.GT:
                        _skip(e, context, "worse than {}".format(pprint(prev_exp)))
                        should_keep = False
                        break
                    else:
                        _skip(e, context, "{} to cached {}".format(
                            "equal" if ordering == Order.EQUAL else "similar",
                            pprint(prev_exp)))
                        assert ordering in (Order.EQUAL, Order.AMBIGUOUS)
                        should_keep = False
                        break

                if should_keep:

                    to_evict = []
                    for (key, exps) in self.cache.items():
                        (p, s, c) = key
                        if p == pool and c in itertools.chain([context], parent_contexts(context)):
                            for ee in exps:
                                if ee.fingerprint == fp and cost_model.compare(e, ee.e, context, pool) == Order.LT:
                                    to_evict.append((key, ee))
                    for key, ee in to_evict:
                        (p, s, c) = key
                        _evict(ee.e, c, e)
                        self.cache[key].remove(ee)
                        self.seen[(c, p, fp)].remove(ee.e)

                    _accept(e, context)
                    seen_key = (context, pool, fp)
                    if seen_key not in self.seen:
                        self.seen[seen_key] = []
                    self.seen[seen_key].append(e)
                    info = EnumeratedExp(
                        e=e,
                        fingerprint=fp,
                        cost=None)
                    res.append(info)
                    yield info

                    with task("accelerating"):
                        to_try = make_random_access(self.heuristics(e, context, pool))
                        if to_try:
                            # print("trying {} accelerations".format(len(to_try)))
                            queue = itertools.chain(to_try, queue)

            # print("EXIT {}".format(k))
            self.in_progress.remove(k)
