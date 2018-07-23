from collections import namedtuple
import itertools

from cozy.common import pick_to_sum, OrderedSet, unique, make_random_access, StopException
from cozy.target_syntax import *
from cozy.syntax_tools import pprint, fresh_var, free_vars, freshen_binders, alpha_equivalent, all_types
from cozy.evaluation import eval_bulk, construct_value
from cozy.typecheck import is_numeric, is_scalar, is_collection
from cozy.cost_model import CostModel, Order
from cozy.pools import Pool, RUNTIME_POOL, STATE_POOL, pool_name
from cozy.contexts import Context, RootCtx, UnderBinder
from cozy.logging import task, task_begin, task_end, event, verbose
from cozy.synthesis.acceleration import histogram

def fingerprint(e : Exp, examples : [{str:object}]):
    return (e.type,) + tuple(eval_bulk(e, examples))

EnumeratedExp = namedtuple("EnumeratedExp", [
    "e",                # The expression
    "fingerprint",      # Its fingerprint
    ])

LITERALS = (T, F, ZERO, ONE)

def of_type(exps, t):
    for e in exps:
        if e.type == t:
            yield e

def collections(exps):
    for e in exps:
        if is_collection(e.type):
            yield e

def belongs_in_context(fvs, context):
    return context is context.generalize(fvs)

def parent_contexts(context):
    while context:
        parent = context.parent()
        yield parent
        context = parent

def _interesting(e, size, context, pool):
    return isinstance(context, RootCtx) and hasattr(e, "_tag")
def _consider(e, size, context, pool):
    if _interesting(e, size, context, pool) and not verbose.value:
        print("considering {} @ size={} in {}/{}".format(pprint(e), size, context, pool_name(pool)))
    task_begin("considering expression", expression=pprint(e), size=size, context=context, pool=pool_name(pool), interesting=_interesting(e, size, context, pool))
def _accept(e, size, context, pool):
    if _interesting(e, size, context, pool) and not verbose.value:
        print("accepting")
    event("accepting {} @ {} in {}/{}".format(pprint(e), size, context, pool_name(pool)))
    task_end()
def _skip(e, size, context, pool, reason):
    if _interesting(e, size, context, pool) and not verbose.value:
        print("skipping [{}]".format(reason))
    event("skipping [{}]".format(reason))
    task_end()
def _evict(e, size, context, pool, better_exp):
    if _interesting(e, size, context, pool) and not verbose.value:
        print("evicting {}".format(pprint(e)))
    event("evicting {}".format(pprint(e)))

def more_specific(ctx1, ctx2):
    a = ctx1
    while a != ctx2:
        a = a.parent()
    if a == ctx2:
        return ctx1
    a = ctx2
    while a != ctx1:
        a = a.parent()
    if a == ctx1:
        return ctx2
    raise ValueError("not common: {}, {}".format(ctx1, ctx2))

def eviction_policy(new_exp : Exp, new_ctx : Context, old_exp : Exp, old_ctx : Context, pool : Pool, cost_model : CostModel) -> [Exp]:
    """Decide which expressions to keep in the cache.

    The returned list contains the new exp, the old exp, or both.
    """
    context = more_specific(new_ctx, old_ctx)
    ordering = cost_model.compare(new_exp, old_exp, context, pool)
    if ordering == Order.LT:        return [new_exp]
    if ordering == Order.GT:        return [old_exp]
    if ordering == Order.EQUAL:     return [old_exp]
    if ordering == Order.AMBIGUOUS: return [new_exp, old_exp]
    raise ValueError(ordering)

class Enumerator(object):
    def __init__(self, examples, cost_model : CostModel, check_wf=None, hints=None, heuristics=None, stop_callback=None, do_eviction=True):
        self.examples = list(examples)
        self.cost_model = cost_model
        self.cache = { } # keys -> [exp]
        self.seen = { }  # (ctx, pool, fp) -> frontier, i.e. [exp]
        self.in_progress = set()
        if check_wf is None:
            check_wf = lambda e, ctx, pool: True
        self.check_wf = check_wf
        if hints is None:
            hints = ()
        self.hints = OrderedSet((e, ctx.generalize(free_vars(e)), p) for (e, ctx, p) in hints)
        if heuristics is None:
            heuristics = lambda e, ctx, pool: ()
        self.heuristics = heuristics
        if stop_callback is None:
            stop_callback = lambda: False
        self.stop_callback = stop_callback
        self.do_eviction = do_eviction

    def cache_size(self):
        return sum(len(v) for v in self.cache.values())

    def heuristic_enumeration(self, context : Context, size : int, pool : Pool) -> [Exp]:
        # lambda-instantiation
        for sz1, sz2 in pick_to_sum(2, size-1):
            for e in self.enumerate(context, sz1, pool):
                for child in e.children():
                    if isinstance(child, ELambda):
                        for arg in self.enumerate(context, sz2, pool):
                            if child.arg.type == arg.type:
                                yield child.apply_to(arg)

        if pool == RUNTIME_POOL:

            # is `x` the last of its kind in `xs`?
            for sz1, sz2 in pick_to_sum(2, size-1):

                for xs in self.enumerate(context, sz1, STATE_POOL):
                    if not is_collection(xs.type):
                        continue

                    h = histogram(xs)
                    h = EStateVar(h).with_type(h.type)
                    for x in of_type(self.enumerate(context, sz2, RUNTIME_POOL), xs.type.t):
                        mg = EMapGet(h, x).with_type(INT)
                        e = EEq(mg, ONE)
                        yield e
                        yield ECond(e,
                            ESingleton(x).with_type(xs.type),
                            EEmptyList().with_type(xs.type)).with_type(xs.type)
                        yield ECond(e,
                            EEmptyList().with_type(xs.type),
                            ESingleton(x).with_type(xs.type)).with_type(xs.type)

            # is `x` the last of its kind in `xs` AND is it argmin
            # according to some interesting function?
            for sz1, sz2 in pick_to_sum(2, size-1):
                for best in self.enumerate(context, sz1, STATE_POOL):
                    if not (isinstance(best, EArgMin) or isinstance(best, EArgMax)):
                        continue

                    h = histogram(best.e)
                    h = EStateVar(h).with_type(h.type)
                    from cozy.structures.heaps import to_heap, EHeapPeek2
                    heap = to_heap(best)
                    heap = EStateVar(heap).with_type(heap.type)
                    for x in of_type(self.enumerate(context, sz2, RUNTIME_POOL), best.type):
                        mg = EMapGet(h, x).with_type(INT)
                        e = EEq(mg, ONE)
                        b = EStateVar(best).with_type(best.type)
                        e = EAll([e, EEq(x, b)])
                        yield e
                        e = ECond(e,
                            EHeapPeek2(heap, EStateVar(ELen(best.e)).with_type(INT)).with_type(best.type),
                            b).with_type(best.type)
                        yield e

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
            for e in LITERALS:
                yield e

            all_interesting_types = OrderedSet()
            for v, _ in context.vars():
                all_interesting_types |= all_types(v)
            for h, _, _ in self.hints:
                all_interesting_types |= all_types(h)
            for t in all_interesting_types:
                l = construct_value(t)
                if l not in LITERALS:
                    yield l

            for (v, p) in context.vars():
                if p == pool:
                    yield v
            for (e, ctx, p) in self.hints:
                if p == pool and ctx.alpha_equivalent(context):
                    yield context.adapt(e, ctx)
            return

        yield from self.heuristic_enumeration(context, size, pool)

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
                yield EUnaryOp("-", e).with_type(e.type)

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
            for l in self.enumerate(context, sz1, pool):
                if not isinstance(l.type, TList):
                    continue
                for i in of_type(self.enumerate(context, sz2, pool), INT):
                    yield EListGet(l, i).with_type(l.type.t)

        for (sz1, sz2, sz3) in pick_to_sum(3, size-1):
            for cond in of_type(self.enumerate(context, sz1, pool), BOOL):
                for then_branch in self.enumerate(context, sz2, pool):
                    for else_branch in of_type(self.enumerate(context, sz2, pool), then_branch.type):
                        yield ECond(cond, then_branch, else_branch).with_type(then_branch.type)

            for l in self.enumerate(context, sz1, pool):
                if not isinstance(l.type, TList):
                    continue
                for st in of_type(self.enumerate(context, sz2, pool), INT):
                    for ed in of_type(self.enumerate(context, sz3, pool), INT):
                        yield EListSlice(l, st, ed).with_type(l.type)

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

        # Let-expressions
        for (sz1, sz2) in pick_to_sum(2, size - 1):
            for x in self.enumerate(context, sz1, pool):
                bag = ESingleton(x).with_type(TBag(x.type))
                for lam in build_lambdas(bag, pool, sz2):
                    e = ELet(x, lam).with_type(lam.body.type)
                    # if x == EBinOp(EVar("x"), "+", EVar("x")):
                    #     e._tag = True
                    yield e

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

        examples = context.instantiate_examples(self.examples)
        if context.parent() is not None:
            for info in self.enumerate_with_info(context.parent(), size, pool):
                e = info.e
                yield EnumeratedExp(
                    e=e,
                    fingerprint=fingerprint(e, examples))

        k = (pool, size, context)
        res = self.cache.get(k)
        if res is not None:
            for e in res:
                yield e
        else:
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
                _consider(e, size, context, pool)

                wf = self.check_wf(e, context, pool)
                if not wf:
                    _skip(e, size, context, pool, "wf={}".format(wf))
                    continue

                fp = fingerprint(e, examples)

                # collect all expressions from parent contexts
                with task("collecting prev exps", size=size, context=context, pool=pool_name(pool)):
                    prev = []
                    for sz in range(0, size+1):
                        prev.extend(self.enumerate_with_info(context, sz, pool))
                    prev = [ p.e for p in prev if p.fingerprint == fp ]

                if any(alpha_equivalent(e, p) for p in prev):
                    _skip(e, size, context, pool, "duplicate")
                    should_keep = False
                else:
                    # decide whether to keep this expression
                    should_keep = True
                    with task("comparing to cached equivalents"):
                        for prev_exp in prev:
                            event("previous: {}".format(pprint(prev_exp)))
                            to_keep = eviction_policy(e, context, prev_exp, context, pool, cost_model)
                            if e not in to_keep:
                                _skip(e, size, context, pool, "preferring {}".format(pprint(prev_exp)))
                                should_keep = False
                                break

                if should_keep:

                    if self.do_eviction:
                        with task("evicting"):
                            to_evict = []
                            for (key, exps) in self.cache.items():
                                (p, s, c) = key
                                if p == pool and c == context:
                                    for ee in exps:
                                        if ee.fingerprint == fp:
                                            event("considering eviction of {}".format(pprint(ee.e)))
                                            to_keep = eviction_policy(e, context, ee.e, c, pool, cost_model)
                                            if ee.e not in to_keep:
                                                to_evict.append((key, ee))
                            for key, ee in to_evict:
                                (p, s, c) = key
                                _evict(ee.e, s, c, pool, e)
                                self.cache[key].remove(ee)
                                self.seen[(c, p, fp)].remove(ee.e)

                    _accept(e, size, context, pool)
                    seen_key = (context, pool, fp)
                    if seen_key not in self.seen:
                        self.seen[seen_key] = []
                    self.seen[seen_key].append(e)
                    info = EnumeratedExp(
                        e=e,
                        fingerprint=fp)
                    res.append(info)
                    yield info

                    with task("accelerating"):
                        to_try = make_random_access(self.heuristics(e, context, pool))
                        if to_try:
                            event("trying {} accelerations of {}".format(len(to_try), pprint(e)))
                            queue = itertools.chain(to_try, queue)

            self.in_progress.remove(k)
