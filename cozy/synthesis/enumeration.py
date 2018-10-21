"""Brute-force enumeration of expressions.

The key definition in this module is `Enumerator`, a class for enumerating
expressions.

The enumerator is very efficient since it implements "equivalence class
deduplication" to avoid visiting different expressions that are semantically
equivalent.

For more information on equivalence class deduplication, see section III.D on
"Enumerative Learning" in the paper

    Syntax-Guided Synthesis
    by Alur et. al.
    published in FMCAD 2013
"""

from collections import namedtuple, defaultdict, OrderedDict
import datetime
import itertools
import functools

from cozy.common import pick_to_sum, OrderedSet, unique, make_random_access, StopException, Periodically
from cozy.syntax import (
    Type, BOOL, INT,
    Exp, ETRUE, EFALSE, ZERO, ONE, EVar, EUnaryOp, UOp, EBinOp, BOp, ECond, EEq,
    TTuple, ETupleGet,
    TRecord, THandle, EGetField,
    TBag, ESingleton,
    TList, EEmptyList, EListGet, EListSlice,
    EIsSubset,
    EArgMin, EArgMax,
    ELet, ELambda)
from cozy.target_syntax import (
    EStateVar,
    EMap, EFilter, EFlatMap,
    TMap, EMakeMap2, EMapKeys, EMapGet, EHasKey)
from cozy.structures import all_extension_handlers
from cozy.syntax_tools import pprint, fresh_var, free_vars, freshen_binders, alpha_equivalent, all_types
from cozy.evaluation import eval_bulk, construct_value, values_equal
from cozy.typecheck import is_numeric, is_scalar, is_collection, is_ordered
from cozy.cost_model import CostModel, Order
from cozy.pools import Pool, RUNTIME_POOL, STATE_POOL, pool_name
from cozy.contexts import Context, RootCtx, UnderBinder, more_specific_context
from cozy.logging import task, task_begin, task_end, event, verbose
from cozy.opts import Option

do_enumerate = Option("enumeration", bool, True,
    description="Enable brute-force enumeration.  "
        + "Disabling this option cripples Cozy, but makes the effect of the "
        + "acceleration rules more apparent.")

@functools.total_ordering
class Fingerprint(object):
    """A summary of an expression's behavior on some inputs.

    An expression's fingerprint is derived from a set of example inputs.  Two
    expressions with different fingerprints are known to behave differently.
    Two expressions with the same fingerprint might be
    semantically equivalent (i.e. behave the same on all inputs), or they might
    just appear to be semantically equivalent on the given inputs.

    The Enumerator class uses fingerprints to group expressions into
    equivalence classes.  It uses fingerprints as keys into a map to quickly
    determine whether a semantically-equivalent version of an expression
    exists.  While fingerprints derived from different example inputs might have
    different sizes, the behavior here is safe since the set of examples is
    fixed at construction time for any one Enumerator class.

    External clients need to be more careful about how they use Fingerprints:
    comparisons between two Fingerprints are meaningless if they were derived
    from different inputs.  Clients also need to be aware that fingerprint
    equality does not imply full semantic equivalence between expressions.
    """
    __slots__ = ("type", "outputs")

    @staticmethod
    def of(e : Exp, inputs : [{str:object}]):
        """Compute the fingerprint of an expression over the given inputs."""
        return Fingerprint(e.type, eval_bulk(e, inputs))

    def __init__(self, type : Type, outputs : [object]):
        self.type = type
        self.outputs = tuple(outputs)

    def _as_tuple(self):
        return (self.type, self.outputs)

    def __hash__(self) -> int:
        return hash(self._as_tuple())

    def __eq__(self, other) -> bool:
        """Test for deep equality.

        Returns true if the fingerprints have the same type and their values
        are deeply equal to each other.

        For information on normal and deep equality, see the documentation for
        compare_values in value_types.py.
        """
        if not isinstance(other, Fingerprint):
            return NotImplemented
        return self._as_tuple() == other._as_tuple()

    def __lt__(self, other) -> bool:
        if not isinstance(other, Fingerprint):
            return NotImplemented
        return self._as_tuple() < other._as_tuple()

    def __len__(self) -> int:
        """Returns the number of examples used to compute this fingerprint."""
        return len(self.outputs)

    def __repr__(self):
        return "Fingerprint{!r}".format(self._as_tuple())

    def __str__(self):
        return "Fingerprint ({}): [{}]".format(pprint(self.type), ", ".join(str(x) for x in self.outputs))

    def _require_comparable_to(self, other):
        if len(self) != len(other):
            raise ValueError("fingerprints have different sizes; were they computed from different sets of examples?")

    def equal_to(self, other) -> bool:
        """Test for normal equality.

        Returns true if the fingerprints have the same type and their values
        are == to each other.

        For information on normal and deep equality, see the documentation for
        compare_values in value_types.py.
        """
        self._require_comparable_to(other)
        return (
            self.type == other.type
            and len(self.outputs) == len(other.outputs)
            and all(values_equal(self.type, v1, v2) for (v1, v2) in zip(self.outputs, other.outputs)))

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
            [{x.id:a, y.id:b} for (a, b) in zip(self.outputs, other.outputs)]))

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

# Debugging routines.
# These serve no functional purpose, but they are useful hooks for developers
# if you need to watch for a particular enumeration event (such as seeing a
# given expression for the first time or evicting a given expression).  Usually
# you will modify _interesting to return True for expressions you are
# interested in.
def _interesting(e, size, context, pool):
    """Is an expression "interesting" for debugging?

    If this returns True, then
     - if Cozy is in verbose mode (--verbose flag), Cozy will print
       "interesting=True" when it starts considering the given expression,
       making the logs easier to search
     - if we are NOT in verbose mode, then Cozy will print log messages about
       the given expression anyway

    The default implementation considers expressions interesting if they are
    in the root context (i.e. not in the body of lambda node) and have the
    "_tag" attribute.

    No expressions have the _tag attribute.  This makes it easy to enable this
    function from other modules by setting
        `expression._tag = True`
    for an expression you are interested in.  Usually it is easier to add a tag
    where an interesting expression gets created than it is to write a
    predicate here that identifies the expression.
    """
    return isinstance(context, RootCtx) and hasattr(e, "_tag")
def _consider(e, size, context, pool):
    """Called when an Enumerator sees an expression for the first time."""
    if _interesting(e, size, context, pool) and not verbose.value:
        print("considering {} @ size={} in {}/{}".format(pprint(e), size, context, pool_name(pool)))
    task_begin("considering expression", expression=pprint(e), size=size, context=context, pool=pool_name(pool), interesting=_interesting(e, size, context, pool))
def _accept(e, size, context, pool, fingerprint):
    """Called when an Enumerator "accepts" an expression and adds it to the cache."""
    if _interesting(e, size, context, pool) and not verbose.value:
        print("accepting [fp={}]".format(fingerprint))
    event("accepting {} @ {} in {}/{}".format(pprint(e), size, context, pool_name(pool)))
    task_end()
def _skip(e, size, context, pool, reason):
    """Called when an Enumerator skips over an expression and does not cache it."""
    if _interesting(e, size, context, pool) and not verbose.value:
        print("skipping [{}]".format(reason))
    event("skipping [{}]".format(reason))
    task_end()
def _evict(e, size, context, pool, better_exp, better_exp_size):
    """Called when an Enumerator evicts a cached expression in favor of a better one."""
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
     - expressions are cached, so enumerating expressions of size N+1 will not
       re-do all the work done while enumerating expressions of size N
     - if two expressions behave the same on all examples, only the better one
       is kept in the cache (although clients might still see the worse one if
       it gets discovered first)
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
                if p == pool:
                    fvs = free_vars(e)
                    if ctx.alpha_equivalent(context.generalize(fvs)):
                        yield context.adapt(e, ctx, e_fvs=fvs)
            return

        if not do_enumerate.value:
            return

        def build_lambdas(bag, pool, body_size):
            v = fresh_var(bag.type.elem_type, omit=set(v for v, p in context.vars()))
            inner_context = UnderBinder(context, v=v, bag=bag, bag_pool=pool)
            for lam_body in self.enumerate(inner_context, body_size, pool):
                yield ELambda(v, lam_body)

        # Load all smaller expressions in this context and pool.
        # cache[S] contains expressions of size S in this context and pool.
        cache = [list(self.enumerate(context, sz, pool)) for sz in range(size)]

        # Enable use of a state-pool expression at runtime
        if pool == RUNTIME_POOL:
            for e in self.enumerate(context.root(), size-1, STATE_POOL):
                yield EStateVar(e).with_type(e.type)

        # Arity-1 expressions
        for e in cache[size-1]:
            if is_collection(e.type):
                elem_type = e.type.elem_type

                yield EEmptyList().with_type(e.type)
                if is_numeric(elem_type):
                    yield EUnaryOp(UOp.Sum, e).with_type(elem_type)

                yield EUnaryOp(UOp.Length, e).with_type(INT)
                yield EUnaryOp(UOp.Empty, e).with_type(BOOL)
                yield EUnaryOp(UOp.Exists, e).with_type(BOOL)
                yield EUnaryOp(UOp.The, e).with_type(elem_type)
                yield EUnaryOp(UOp.Distinct, e).with_type(e.type)
                yield EUnaryOp(UOp.AreUnique, e).with_type(BOOL)

                if elem_type == BOOL:
                    yield EUnaryOp(UOp.Any, e).with_type(BOOL)
                    yield EUnaryOp(UOp.All, e).with_type(BOOL)

            yield ESingleton(e).with_type(TBag(e.type))

            if isinstance(e.type, TRecord):
                for (f,t) in e.type.fields:
                    yield EGetField(e, f).with_type(t)

            if isinstance(e.type, THandle):
                yield EGetField(e, "val").with_type(e.type.value_type)

            if isinstance(e.type, TTuple):
                for n in range(len(e.type.ts)):
                    yield ETupleGet(e, n).with_type(e.type.ts[n])

            if e.type == BOOL:
                yield EUnaryOp(UOp.Not, e).with_type(BOOL)

            if is_numeric(e.type):
                yield EUnaryOp("-", e).with_type(e.type)

            if isinstance(e.type, TMap):
                yield EMapKeys(e).with_type(TBag(e.type.k))

        # Arity-2 expressions
        for (sz1, sz2) in pick_to_sum(2, size - 1):
            # sz1 + sz2 = size - 1
            for e1 in cache[sz1]:
                t = e1.type

                if is_numeric(t):
                    for a2 in of_type(cache[sz2], t):
                        yield EBinOp(e1, "+", a2).with_type(t)
                        yield EBinOp(e1, "-", a2).with_type(t)

                if is_ordered(t):
                    for a2 in of_type(cache[sz2], t):
                        yield EBinOp(e1, ">", a2).with_type(BOOL)
                        yield EBinOp(e1, "<", a2).with_type(BOOL)
                        yield EBinOp(e1, ">=", a2).with_type(BOOL)
                        yield EBinOp(e1, "<=", a2).with_type(BOOL)

                if t == BOOL:
                    for a2 in of_type(cache[sz2], BOOL):
                        yield EBinOp(e1, BOp.And, a2).with_type(BOOL)
                        yield EBinOp(e1, BOp.Or, a2).with_type(BOOL)

                if not isinstance(t, TMap):
                    for a2 in of_type(cache[sz2], t):
                        yield EEq(e1, a2)
                        yield EBinOp(e1, "!=", a2).with_type(BOOL)

                if isinstance(t, TMap):
                    for k in of_type(cache[sz2], t.k):
                        yield EMapGet(e1, k).with_type(t.v)
                        yield EHasKey(e1, k).with_type(BOOL)

                if isinstance(t, TList):
                    for i in of_type(cache[sz2], INT):
                        yield EListGet(e1, i).with_type(e1.type.elem_type)

                if is_collection(t):
                    elem_type = t.elem_type
                    for e2 in of_type(cache[sz2], t):
                        yield EBinOp(e1, "+", e2).with_type(t)
                        yield EBinOp(e1, "-", e2).with_type(t)
                    for e2 in of_type(cache[sz2], elem_type):
                        yield EBinOp(e2, BOp.In, e1).with_type(BOOL)
                    for f in build_lambdas(e1, pool, sz2):
                        body_type = f.body.type
                        yield EMap(e1, f).with_type(TBag(body_type))
                        if body_type == BOOL:
                            yield EFilter(e1, f).with_type(t)
                        if is_numeric(body_type):
                            yield EArgMin(e1, f).with_type(elem_type)
                            yield EArgMax(e1, f).with_type(elem_type)
                        if is_collection(body_type):
                            yield EFlatMap(e1, f).with_type(TBag(body_type.elem_type))

                        if pool == STATE_POOL and is_scalar(elem_type):
                            yield EMakeMap2(e1, f).with_type(TMap(elem_type, body_type))

                e1_singleton = ESingleton(e1).with_type(TBag(e1.type))
                for f in build_lambdas(e1_singleton, pool, sz2):
                    yield ELet(e1, f).with_type(f.body.type)

        # Arity-3 expressions
        for (sz1, sz2, sz3) in pick_to_sum(3, size-1):
            # sz1 + sz2 + sz3 = size - 1
            for e1 in cache[sz1]:
                if e1.type == BOOL:
                    cond = e1
                    for then_branch in cache[sz2]:
                        for else_branch in of_type(cache[sz2], then_branch.type):
                            yield ECond(cond, then_branch, else_branch).with_type(then_branch.type)
                if isinstance(e1.type, TList):
                    for start in of_type(cache[sz2], INT):
                        for end in of_type(cache[sz3], INT):
                            yield EListSlice(e1, start, end).with_type(e1.type)

        for h in all_extension_handlers():
            yield from h.enumerate(context, size, pool, self.enumerate, build_lambdas)

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
        """Returns a context that is equivalent to this one.

        This canonical representative is the one used in the cache.
        """
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
            assert k not in self.in_progress, "recursive enumeration?? {}".format(k)
            self.in_progress.add(k)
            yield from self._enumerate_with_info(context, size, pool)
            self.in_progress.remove(k)
            self.complete.add(k)

    def _enumerate_with_info(self, context : Context, size : int, pool : Pool) -> [EnumeratedExp]:
        """Helper for enumerate_with_info that bypasses the cache.

        Note that this method DOES affect the cache: it writes its output into
        the cache and may do evictions.  The enumerate_with_info method ensures
        that there is only ever one call to this method for a given (context,
        size, pool).
        """

        examples = context.instantiate_examples(self.examples)
        cache = self.cache
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

    def expressions_may_exist_above_size(self, context, pool, size):
        """Returns true if expressions larger than `size` might exist.

        If this method returns false, then all calls to `enumerate` or
        `enumerate_with_info` with sizes strictly larger than the given size
        will yield no results.
        """

        if size <= 0:
            return True

        maximum_arity = 3 # TODO: adjust this later?
        for arity in range(1, maximum_arity+1):
            for split in pick_to_sum(arity, size):
                for exprs in itertools.product(*(self.enumerate(context, sz, pool) for sz in split)):
                    return True
        if pool == RUNTIME_POOL:
            return self.expressions_may_exist_above_size(context.root(), STATE_POOL, size-1)
        return False
