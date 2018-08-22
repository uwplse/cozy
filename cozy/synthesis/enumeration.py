"""Brute-force enumeration of expressions.

The key definition in this module is `Enumerator`, a class for enumerating
expressions.
"""

from collections import namedtuple, defaultdict, OrderedDict
import datetime
import itertools
import functools

from cozy.common import pick_to_sum, OrderedSet, unique, make_random_access, StopException, Periodically
from cozy.target_syntax import *
from cozy.syntax_tools import pprint, fresh_var, free_vars, freshen_binders, alpha_equivalent, all_types
from cozy.evaluation import eval_bulk, construct_value, values_equal
from cozy.typecheck import is_numeric, is_scalar, is_collection
from cozy.cost_model import CostModel, Order
from cozy.pools import Pool, RUNTIME_POOL, STATE_POOL, pool_name
from cozy.contexts import Context, RootCtx, UnderBinder, more_specific_context
from cozy.logging import task, task_begin, task_end, event, verbose

@functools.total_ordering
class Fingerprint(object):
    """A fuzzy identifier for an expression.

    An expression's fingerprint is derived from a set of example inputs.  Two
    expressions with different fingerprints definitely behave differently in
    some cases.  Two expressions with the same fingerprint might be
    semantically equivalent (i.e. behave the same on all inputs), or they might
    just appear to be semantically equivalent on the given examples.

    The Enumerator class uses fingerprints to group expressions into
    equivalence classes.
    """
    __slots__ = ("type", "signature")

    @staticmethod
    def of(e : Exp, inputs : [{str:object}]):
        """Compute the fingerprint of an expression."""
        return Fingerprint(e.type, eval_bulk(e, inputs))

    def __init__(self, type : Type, signature : [object]):
        self.type = type
        self.signature = tuple(signature)

    def _as_tuple(self):
        return (self.type, self.signature)

    def __hash__(self) -> int:
        return hash(self._as_tuple())

    def __eq__(self, other) -> bool:
        if not isinstance(other, Fingerprint):
            return NotImplemented
        return self._as_tuple() == other._as_tuple()

    def __lt__(self, other) -> bool:
        if not isinstance(other, Fingerprint):
            return NotImplemented
        return self._as_tuple() < other._as_tuple()

    def __len__(self) -> int:
        """Returns the number of examples used to compute this fingerprint."""
        return len(self.signature)

    def __repr__(self):
        return "Fingerprint{!r}".format(self._as_tuple())

    def __str__(self):
        return "Fingerprint ({}): [{}]".format(pprint(self.type), ", ".join(str(x) for x in self.signature))

    def _require_comparable_to(self, other):
        if len(self) != len(other):
            raise ValueError("fingerprints have different sizes; were they computed from different sets of examples?")

    def equal_to(self, other) -> bool:
        """Determine whether two fingerprints are very similar.

        If this returns True, then expressions with the given fingerprints look
        to be == to each other (that's the Cozy ==, not Python ==), but not
        necessarily === to each other (that's Cozy ===; Python has no ===).

        Clients should use this instead of Python's == operator.
        Comparing two fingerprint objects directly with Python's == operator
        checks whether expressions with those fingerprints look to be === to
        each other.
        """
        self._require_comparable_to(other)
        return (
            self.type == other.type
            and len(self.signature) == len(other.signature)
            and all(values_equal(self.type, v1, v2) for (v1, v2) in zip(self.signature, other.signature)))

    def subset_of(self, other) -> bool:
        """Determine whether this fingerprint looks like a subset of the other.

        If this returns True, then it could be the case that an expression with
        this fingerprint always returns a strict subset of the elements that
        would be returned by an expression with the other fingerprint.
        """
        if not is_collection(self.type):
            raise ValueError("this fingerprint is not for a collection-type expression")
        if not is_collection(other.type):
            raise ValueError("other fingerprint is not for a collection-type expression")
        self._require_comparable_to(other)
        x = EVar("x").with_type(self.type)
        y = EVar("y").with_type(other.type)
        is_subset = EIsSubset(x, y)
        return all(eval_bulk(
            is_subset,
            [{x.id:a, y.id:b} for (a, b) in zip(self.signature, other.signature)]))

EnumeratedExp = namedtuple("EnumeratedExp", [
    "e",                # The expression
    "fingerprint",      # Its fingerprint
    "size",             # The size at which the expression was first discovered
    ])

LITERALS = (ETRUE, EFALSE, ZERO, ONE)

def of_type(exps : [Exp], t : Type):
    """Filter `exps` to expressions of the given type."""
    for e in exps:
        if e.type == t:
            yield e

def collections(exps : [Exp]):
    """Filter `exps` to collection-type expressions."""
    for e in exps:
        if is_collection(e.type):
            yield e

def belongs_in_context(fvs, context):
    return context is context.generalize(fvs)

# Debugging routines.
# These serve no functional purpose, but they are useful hooks for developers
# if you need to watch for a particular enumeration event (such as seeing a
# given expression for the first time or evicting a given expression).
def _interesting(e, size, context, pool):
    return isinstance(context, RootCtx) and hasattr(e, "_tag")
def _consider(e, size, context, pool):
    if _interesting(e, size, context, pool) and not verbose.value:
        print("considering {} @ size={} in {}/{}".format(pprint(e), size, context, pool_name(pool)))
    task_begin("considering expression", expression=pprint(e), size=size, context=context, pool=pool_name(pool), interesting=_interesting(e, size, context, pool))
def _accept(e, size, context, pool, fingerprint):
    if _interesting(e, size, context, pool) and not verbose.value:
        print("accepting [fp={}]".format(fingerprint))
    event("accepting {} @ {} in {}/{}".format(pprint(e), size, context, pool_name(pool)))
    task_end()
def _skip(e, size, context, pool, reason):
    if _interesting(e, size, context, pool) and not verbose.value:
        print("skipping [{}]".format(reason))
    event("skipping [{}]".format(reason))
    task_end()
def _evict(e, size, context, pool, better_exp, better_exp_size):
    if _interesting(e, size, context, pool) and not verbose.value:
        print("evicting {}".format(pprint(e)))
    elif _interesting(better_exp, better_exp_size, context, pool) and not verbose.value:
        print("{} caused eviction of {}".format(pprint(better_exp), pprint(e)))
    event("evicting {}".format(pprint(e)))

def eviction_policy(new_exp : Exp, new_ctx : Context, old_exp : Exp, old_ctx : Context, pool : Pool, cost_model : CostModel) -> [Exp]:
    """Decide which expressions to keep in the cache.

    The returned list contains the new exp, the old exp, or both.
    """
    context = more_specific_context(new_ctx, old_ctx)
    ordering = cost_model.compare(new_exp, old_exp, context, pool)
    if ordering == Order.LT:        return [new_exp]
    if ordering == Order.GT:        return [old_exp]
    if ordering == Order.EQUAL:     return [old_exp]
    if ordering == Order.AMBIGUOUS: return [new_exp, old_exp]
    raise ValueError(ordering)

class ExpCache(object):
    """Cache for expressions used by Enumerator instances."""

    def __init__(self):
        """Construct an empty cache."""
        self.data = OrderedDict() # (Pool, Context) -> (int -> [EnumeratedExp], Fingerprint -> [EnumeratedExp])

    def __len__(self):
        """Return the total number of cached expressions across all contexts and pools."""
        return sum(sum(len(l) for l in d.values()) for d, _ in self.data.values())

    def add(self, context : Context, pool : Pool, enumerated_exp : EnumeratedExp):
        """Insert an expression into the cache for a given context and pool.

        This method will happily insert duplicate expressions into the cache.
        """
        key = (pool, context)
        storage = self.data.get(key)
        if storage is None:
            storage = (defaultdict(list), defaultdict(list))
            self.data[key] = storage
        by_size, by_fingerprint = storage
        by_size[enumerated_exp.size].append(enumerated_exp)
        by_fingerprint[enumerated_exp.fingerprint].append(enumerated_exp)

    def remove(self, context : Context, pool : Pool, enumerated_exp : EnumeratedExp):
        """Remove an expression from the cache for a given context and pool.

        This method requires that the expression already exist in the cache.
        Only one copy is removed if multiple copies are present.
        """
        key = (pool, context)
        by_size, by_fingerprint = self.data[key]
        by_size[enumerated_exp.size].remove(enumerated_exp)
        by_fingerprint[enumerated_exp.fingerprint].remove(enumerated_exp)

    def all_contexts(self) -> [Context]:
        """Iterate over the unique contexts that the cache has seen."""
        return unique(context for pool, context in self.data.keys())

    def find_expressions_of_size(self, context : Context, pool : Pool, size : int) -> [EnumeratedExp]:
        """Iterate over all expressions of the given size in the given context and pool."""
        key = (pool, context)
        yield from self.data.get(key, ({}, {}))[0].get(size, ())

    def find_equivalent_expressions(self, context : Context, pool : Pool, fingerprint : Fingerprint) -> [EnumeratedExp]:
        """Iterate over all expressions with the given fingerprint in the given context and pool."""
        key = (pool, context)
        yield from self.data.get(key, ({}, {}))[1].get(fingerprint, ())

class Enumerator(object):
    """Brute-force enumerator for expressions in order of AST size.

    This class has lots of useful features:
     - it uses a set of example inputs to deduplicate expressions via "fingerprints"
     - expressions are cached so that less deduplication work needs to happen
     - if two expressions behave the same on all examples, only the better one
       is kept
    """

    def __init__(self, examples, cost_model : CostModel, check_wf=None, hints=None, heuristics=None, stop_callback=None, do_eviction=True):
        """Set up a fresh enumerator.

        Parameters:
         - examples: a set of example inputs to deduplicate expressions
         - cost_model: a cost model to tell us which expressions to prefer
         - check_wf: an optional additional filter to restrict which expressions
           are visited
         - hints: extra expressions to visit first
         - heuristics: an optional function to improve visited expressions
         - stop_callback: a function that is checked periodically to stop
           enumeration
         - do_eviction: boolean. if true, this class spends time
           trying to evict older, slower versions of expressions from its cache
        """
        self.examples = list(examples)
        self.cost_model = cost_model
        self.cache = ExpCache()
        self.in_progress = set()
        self.complete = set()
        if check_wf is None:
            check_wf = lambda e, ctx, pool: True
        self.check_wf = check_wf
        if hints is None:
            hints = ()
        self.hints = OrderedSet((e, ctx.generalize(free_vars(e)), p) for (e, ctx, p) in hints)
        self.hint_types = OrderedSet()
        for h, _, _ in self.hints:
            self.hint_types |= all_types(h)
        if heuristics is None:
            heuristics = lambda e, ctx, pool: ()
        self.heuristics = heuristics
        if stop_callback is None:
            stop_callback = lambda: False
        self.stop_callback = stop_callback
        self.do_eviction = do_eviction
        self.stat_timer = Periodically(self.print_stats, timespan=datetime.timedelta(seconds=2))

    def print_stats(self):
        print("  |cache|={}".format(self.cache_size()))

    def cache_size(self):
        return len(self.cache)

    def _enumerate_core(self, context : Context, size : int, pool : Pool) -> [Exp]:
        """Build new expressions of the given size.

        Arguments:
            context : a Context object describing the vars in scope
            size    : size of expressions to enumerate; each expression in
                      the output will have this size
            pool    : pool to enumerate

        This function is not cached.  Clients should call `enumerate` instead.
        """

        if size < 0:
            return

        if size == 0:
            for e in LITERALS:
                yield e

            all_interesting_types = OrderedSet(self.hint_types)
            for v, _ in context.vars():
                all_interesting_types |= all_types(v.type)
            for t in all_interesting_types:
                l = construct_value(t)
                if l not in LITERALS:
                    yield l

            for (v, p) in context.vars():
                if p == pool:
                    yield v
            for (e, ctx, p) in self.hints:
                fvs = free_vars(e)
                if p == pool and ctx.alpha_equivalent(context.generalize(fvs)):
                    yield context.adapt(e, ctx, e_fvs=fvs)
            return

        # load all smaller expressions in this context and pool
        # cache[S] contains expressions of size S in this context and pool
        cache = [list(self.enumerate(context, sz, pool)) for sz in range(size)]

        for e in collections(cache[size-1]):
            yield EEmptyList().with_type(e.type)
            if is_numeric(e.type.elem_type):
                yield EUnaryOp(UOp.Sum, e).with_type(e.type.elem_type)

        for e in cache[size-1]:
            yield ESingleton(e).with_type(TBag(e.type))

        for e in cache[size-1]:
            if isinstance(e.type, TRecord):
                for (f,t) in e.type.fields:
                    yield EGetField(e, f).with_type(t)

        for e in cache[size-1]:
            if isinstance(e.type, THandle):
                yield EGetField(e, "val").with_type(e.type.value_type)

        for e in cache[size-1]:
            if isinstance(e.type, TTuple):
                for n in range(len(e.type.ts)):
                    yield ETupleGet(e, n).with_type(e.type.ts[n])

        for e in of_type(cache[size-1], BOOL):
            yield EUnaryOp(UOp.Not, e).with_type(BOOL)

        for e in cache[size-1]:
            if is_numeric(e.type):
                yield EUnaryOp("-", e).with_type(e.type)

        for m in cache[size-1]:
            if isinstance(m.type, TMap):
                yield EMapKeys(m).with_type(TBag(m.type.k))

        for (sz1, sz2) in pick_to_sum(2, size - 1):
            # sz1 + sz2 = size - 1
            for a1 in cache[sz1]:
                t = a1.type
                if not is_numeric(t):
                    continue
                for a2 in of_type(cache[sz2], t):
                    yield EBinOp(a1, "+", a2).with_type(t)
                    yield EBinOp(a1, "-", a2).with_type(t)
                    yield EBinOp(a1, ">", a2).with_type(BOOL)
                    yield EBinOp(a1, "<", a2).with_type(BOOL)
                    yield EBinOp(a1, ">=", a2).with_type(BOOL)
                    yield EBinOp(a1, "<=", a2).with_type(BOOL)
            for a1 in collections(cache[sz1]):
                for a2 in of_type(cache[sz2], a1.type):
                    yield EBinOp(a1, "+", a2).with_type(a1.type)
                    yield EBinOp(a1, "-", a2).with_type(a1.type)
                for a2 in of_type(cache[sz2], a1.type.elem_type):
                    yield EBinOp(a2, BOp.In, a1).with_type(BOOL)
            for a1 in of_type(cache[sz1], BOOL):
                for a2 in of_type(cache[sz2], BOOL):
                    yield EBinOp(a1, BOp.And, a2).with_type(BOOL)
                    yield EBinOp(a1, BOp.Or, a2).with_type(BOOL)
            for a1 in cache[sz1]:
                if not isinstance(a1.type, TMap):
                    for a2 in of_type(cache[sz2], a1.type):
                        yield EEq(a1, a2)
                        yield EBinOp(a1, "!=", a2).with_type(BOOL)
            for m in cache[sz1]:
                if isinstance(m.type, TMap):
                    for k in of_type(cache[sz2], m.type.k):
                        yield EMapGet(m, k).with_type(m.type.v)
                        yield EHasKey(m, k).with_type(BOOL)
            for l in cache[sz1]:
                if not isinstance(l.type, TList):
                    continue
                for i in of_type(cache[sz2], INT):
                    yield EListGet(l, i).with_type(l.type.elem_type)

        for (sz1, sz2, sz3) in pick_to_sum(3, size-1):
            # sz1 + sz2 + sz3 = size - 1
            for cond in of_type(cache[sz1], BOOL):
                for then_branch in cache[sz2]:
                    for else_branch in of_type(cache[sz2], then_branch.type):
                        yield ECond(cond, then_branch, else_branch).with_type(then_branch.type)

            for l in cache[sz1]:
                if not isinstance(l.type, TList):
                    continue
                for st in of_type(cache[sz2], INT):
                    for ed in of_type(cache[sz3], INT):
                        yield EListSlice(l, st, ed).with_type(l.type)

        for bag in collections(cache[size-1]):
            yield EUnaryOp(UOp.Length, bag).with_type(INT)
            yield EUnaryOp(UOp.Empty, bag).with_type(BOOL)
            yield EUnaryOp(UOp.Exists, bag).with_type(BOOL)
            yield EUnaryOp(UOp.The, bag).with_type(bag.type.elem_type)
            yield EUnaryOp(UOp.Distinct, bag).with_type(bag.type)
            yield EUnaryOp(UOp.AreUnique, bag).with_type(BOOL)

            if bag.type.elem_type == BOOL:
                yield EUnaryOp(UOp.Any, bag).with_type(BOOL)
                yield EUnaryOp(UOp.All, bag).with_type(BOOL)

        def build_lambdas(bag, pool, body_size):
            v = fresh_var(bag.type.elem_type, omit=set(v for v, p in context.vars()))
            inner_context = UnderBinder(context, v=v, bag=bag, bag_pool=pool)
            for lam_body in self.enumerate(inner_context, body_size, pool):
                yield ELambda(v, lam_body)

        # Let-expressions
        for (sz1, sz2) in pick_to_sum(2, size - 1):
            for x in cache[sz1]:
                bag = ESingleton(x).with_type(TBag(x.type))
                for lam in build_lambdas(bag, pool, sz2):
                    yield ELet(x, lam).with_type(lam.body.type)

        # Iteration
        for (sz1, sz2) in pick_to_sum(2, size - 1):
            for bag in collections(cache[sz1]):
                for lam in build_lambdas(bag, pool, sz2):
                    body_type = lam.body.type
                    yield EMap(bag, lam).with_type(TBag(body_type))
                    if body_type == BOOL:
                        yield EFilter(bag, lam).with_type(bag.type)
                    if is_numeric(body_type):
                        yield EArgMin(bag, lam).with_type(bag.type.elem_type)
                        yield EArgMax(bag, lam).with_type(bag.type.elem_type)
                    if is_collection(body_type):
                        yield EFlatMap(bag, lam).with_type(TBag(body_type.elem_type))

        # Enable use of a state-pool expression at runtime
        if pool == RUNTIME_POOL:
            for e in self.enumerate(context.root(), size-1, STATE_POOL):
                yield EStateVar(e).with_type(e.type)

        # Create maps
        if pool == STATE_POOL:
            for (sz1, sz2) in pick_to_sum(2, size - 1):
                for bag in collections(self.enumerate(context, sz1, STATE_POOL)):
                    if not is_scalar(bag.type.elem_type):
                        continue
                    for lam in build_lambdas(bag, STATE_POOL, sz2):
                        t = TMap(bag.type.elem_type, lam.body.type)
                        m = EMakeMap2(bag, lam).with_type(t)
                        yield m

    def enumerate(self, context : Context, size : int, pool : Pool) -> [Exp]:
        """Enumerate expressions of the given size.

        The output of this function is cached, so subsequent calls are very
        cheap.

        Arguments:
            context : a Context object describing the vars in scope
            size    : size of expressions to enumerate
            pool    : expression pool to visit
        """
        for info in self.enumerate_with_info(context, size, pool):
            # enumerate_with_info yields more information than needed here.
            # Just yield part of it.
            yield info.e

    def canonical_context(self, context):
        # TODO: deduplicate based on examples, not alpha equivalence
        for ctx in self.cache.all_contexts():
            if ctx != context and ctx.alpha_equivalent(context):
                return ctx
        return context

    def enumerate_with_info(self, context : Context, size : int, pool : Pool) -> [EnumeratedExp]:
        """Enumerate expressions (and fingerprints) of the given size.

        The output of this function is cached, so subsequent calls are very
        cheap.

        Arguments:
            context : a Context object describing the vars in scope
            size    : size of expressions to enumerate
            pool    : expression pool to visit
        """

        canonical_context = self.canonical_context(context)
        if canonical_context is not context:
            print("adapting request: {} ---> {}".format(context, canonical_context))
            for info in self.enumerate_with_info(canonical_context, size, pool):
                yield info._replace(e=context.adapt(info.e, canonical_context))
            return

        k = (pool, size, context)
        cache = self.cache

        if k in self.complete:
            yield from cache.find_expressions_of_size(context, pool, size)
        else:
            examples = context.instantiate_examples(self.examples)
            assert k not in self.in_progress, "recursive enumeration?? {}".format(k)
            self.in_progress.add(k)
            queue = self._enumerate_core(context, size, pool)
            cost_model = self.cost_model
            while True:
                if self.stop_callback():
                    raise StopException()

                try:
                    e = next(queue)
                except StopIteration:
                    break

                self.stat_timer.check()

                e = freshen_binders(e, context)
                _consider(e, size, context, pool)

                wf = self.check_wf(e, context, pool)
                if not wf:
                    _skip(e, size, context, pool, "wf={}".format(wf))
                    continue

                fp = Fingerprint.of(e, examples)

                # collect all expressions from parent contexts
                prev = list(cache.find_equivalent_expressions(context, pool, fp))
                to_evict = []

                if any(e.type == prev_entry.e.type and alpha_equivalent(e, prev_entry.e) for prev_entry in prev):
                    _skip(e, size, context, pool, "duplicate")
                    should_keep = False
                else:
                    # decide whether to keep this expression
                    should_keep = True
                    if prev:
                        with task("comparing to cached equivalents", count=len(prev)):
                            for entry in prev:
                                prev_exp = entry.e
                                event("previous: {}".format(pprint(prev_exp)))
                                to_keep = eviction_policy(e, context, prev_exp, context, pool, cost_model)
                                if e not in to_keep:
                                    _skip(e, size, context, pool, "preferring {}".format(pprint(prev_exp)))
                                    should_keep = False
                                    break
                                if prev_exp not in to_keep:
                                    to_evict.append(entry)

                assert not (to_evict and not should_keep)

                if should_keep:

                    if self.do_eviction and to_evict:
                        with task("evicting", count=to_evict):
                            for entry in to_evict:
                                _evict(entry.e, entry.size, context, pool, e, size)
                                cache.remove(context, pool, entry)

                    _accept(e, size, context, pool, fp)
                    info = EnumeratedExp(
                        e=e,
                        fingerprint=fp,
                        size=size)
                    yield info
                    cache.add(context, pool, info)

                    if size == 0:
                        with task("accelerating"):
                            to_try = make_random_access(self.heuristics(e, context, pool))
                            if to_try:
                                event("trying {} accelerations of {}".format(len(to_try), pprint(e)))
                                queue = itertools.chain(to_try, queue)

            self.in_progress.remove(k)
            self.complete.add(k)
