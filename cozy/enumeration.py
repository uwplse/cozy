from collections import namedtuple, OrderedDict
from enum import Enum
import itertools

from cozy.common import pick_to_sum, OrderedSet, FrozenDict, unique
from cozy.target_syntax import *
from cozy.syntax_tools import pprint, fresh_var, all_exps, strip_EStateVar, free_vars, alpha_equivalent, subst
from cozy.evaluation import eval_bulk
from cozy.synthesis.cache import Cache, SeenSet
from cozy.typecheck import is_numeric, is_scalar, is_collection
from cozy.cost_model import CostModel, Cost
from cozy.pools import Pool, ALL_POOLS, RUNTIME_POOL, STATE_POOL, pool_name
from cozy.opts import Option

use_cost_ceiling = Option("cost-ceiling", bool, True)
hyperaggressive_eviction = Option("hyperaggressive-eviction", bool, False)

def fingerprint(e : Exp, examples : [{str:object}]):
    return (e.type,) + tuple(eval_bulk(e, examples))

StartMinorIteration = namedtuple("StartMinorIteration", [
    "size",
    "cache_size"])
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

class ExpEvent(Enum):
    CONSIDER = 0
    SKIP     = 1
    ACCEPT   = 2
    EVICT    = 3

oracle = EBinOp(
    ESingleton(EGetField(EVar('x').with_type(THandle('H', TInt())), 'val')), '-',
    EUnaryOp('distinct', EMap(EBinOp(EStateVar(EVar('xs').with_type(TBag(THandle('H', TInt())))), '-', ESingleton(EVar('x').with_type(THandle('H', TInt())))), ELambda(EVar('_var4').with_type(THandle('H', TInt())), EGetField(EVar('_var4').with_type(THandle('H', TInt())), 'val')))))
def _interesting(depth : int, e : Exp, pool : Pool, event : ExpEvent):
    return False
    # from cozy.syntax_tools import alpha_equivalent
    # if depth > 0:
    #     return False
    # return True
    # return oracle is not None and any(alpha_equivalent(e, x) for x in all_exps(oracle))
    return hasattr(e, "_tag")
    # return False
    # return depth == 0 # and (isinstance(e, EMakeMap2) or isinstance(e, EMapGet))

def _on_consider(depth : int, e : Exp, pool : Pool):
    if _interesting(depth, e, pool, ExpEvent.CONSIDER):
        print(" > considering {} in {}".format(pprint(e), pool_name(pool)))

def _on_skip(depth : int, e : Exp, pool : Pool, reason : str, **data):
    if _interesting(depth, e, pool, ExpEvent.SKIP):
        print("   > skipping {}; {}".format(pprint(e), reason))
        for k, v in data.items():
            print("         > {} = {}".format(k, pprint(v) if isinstance(v, Exp) else v))

def _on_evict(depth : int, e : Exp, pool : Pool, better_alternative : Exp, better_cost : Cost):
    if _interesting(depth, e, pool, ExpEvent.EVICT):
        print("   > evicting {}; {}".format(pprint(e), pprint(better_alternative)))

def _on_accept(depth : int, e : Exp, pool : Pool, fp):
    if _interesting(depth, e, pool, ExpEvent.ACCEPT):
        print("   > accepting {} in {} : {}".format(pprint(e), pool_name(pool), pprint(e.type)))
        # print("     fp = {!r}".format(fp))

def of_type(exps, t):
    for e in exps:
        if e.type == t:
            yield e

def collections(exps):
    for e in exps:
        if is_collection(e.type):
            yield e

class Context(object):
    def vars(self) -> {(EVar, Pool)}:
        raise NotImplementedError()
    def parent(self):
        raise NotImplementedError()
    def legal_for(self, fvs : {EVar}) -> bool:
        vs = {v for (v, pool) in self.vars()}
        return all(v in vs for v in fvs)
    def instantiate_examples(self, examples : [dict]) -> [dict]:
        raise NotImplementedError()
    def alpha_equivalent(self, other) -> bool:
        raise NotImplementedError()
    def adapt(self, e : Exp, ctx) -> Exp:
        raise NotImplementedError()

class RootCtx(Context):
    def __init__(self, state_vars : [Exp], args : [Exp]):
        self.state_vars = OrderedSet(state_vars)
        self.args = OrderedSet(args)
        assert not (self.state_vars & self.args)
    def vars(self):
        return OrderedSet(itertools.chain(
            [(v, STATE_POOL)   for v in self.state_vars],
            [(v, RUNTIME_POOL) for v in self.args]))
    def parent(self):
        return None
    def instantiate_examples(self, examples : [dict]) -> [dict]:
        return examples
    def alpha_equivalent(self, other):
        return self == other
    def adapt(self, e : Exp, ctx) -> Exp:
        return e
    def __hash__(self):
        return hash((tuple(self.state_vars), tuple(self.args)))
    def __eq__(self, other):
        return isinstance(other, RootCtx) and (self.state_vars, self.args) == (other.state_vars, other.args)
    def __repr__(self):
        return "RootCtx(state_vars={!r}, args={!r})".format(self.state_vars, self.args)
    def __str__(self):
        return "(root)"

class UnderBinder(Context):
    def __init__(self, parent : Context, v : EVar, bag : Exp, bag_pool : Pool):
        assert v.type == bag.type.t
        assert parent.legal_for(free_vars(bag))
        self._parent = parent
        self.var = v
        self.bag = bag
        self.pool = bag_pool
    def vars(self):
        return self._parent.vars() | {(self.var, self.pool)}
    def parent(self):
        return self._parent
    def instantiate_examples(self, examples : [dict]) -> [dict]:
        inst = self._parent.instantiate_examples(examples)
        res = []
        for ex in inst:
            vals, = eval_bulk(self.bag, [ex])
            for v in unique(vals):
                ex = dict(ex)
                ex[self.var.id] = v
                res.append(ex)
        return res
    def alpha_equivalent(self, other):
        if not isinstance(other, UnderBinder):
            return False
        if not self.var.type == other.var.type:
            return False
        if not self._parent.alpha_equivalent(other._parent):
            return False
        return alpha_equivalent(self.bag, self._parent.adapt(other.bag, other._parent))
    def adapt(self, e : Exp, ctx) -> Exp:
        # assert self.alpha_equivalent(ctx) # slow!
        assert isinstance(ctx, UnderBinder)
        e = self._parent.adapt(e, ctx._parent)
        return subst(e, { ctx.var.id : self.var })
    def __hash__(self):
        return hash((self._parent, self.var, self.bag, self.pool))
    def __eq__(self, other):
        return isinstance(other, UnderBinder) and (self._parent, self.var, self.bag, self.pool) == (other._parent, other.var, other.bag, other.pool)
    def __repr__(self):
        return "UnderBinder(parent={}, v={}, bag={}, bag_pool={})".format(self._parent, self.var, self.bag, self.pool)
    def __str__(self):
        return "{} in {}, {}".format(self.var.id, pprint(self.bag), self._parent)

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

class Enumerator(object):
    def __init__(self, examples, cost_model):
        self.examples = examples
        self.cost_model = cost_model
        self.cache = { } # keys -> [exp]
        self.seen = { }  # (ctx, pool, fp) -> frontier, i.e. [exp]
        self.in_progress = set()

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
            v = fresh_var(bag.type.t)
            inner_context = UnderBinder(context, v=v, bag=bag, bag_pool=pool)
            for lam_body in self.enumerate(inner_context, body_size, pool):
                yield ELambda(v, lam_body)

        # Iteration
        for (sz1, sz2) in pick_to_sum(2, size - 1):
            for bag in collections(self.enumerate(context, sz1, STATE_POOL)):
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

    def key(self, examples, size, pool):
        return (pool, size, tuple(FrozenDict(ex) for ex in examples))

    def known_contexts(self):
        return unique(ctx for (ctx, pool, fp) in self.seen.keys())

    def enumerate_with_info(self, context : Context, size : int, pool : Pool) -> [EnumeratedExp]:
        for ctx in self.known_contexts():
            if ctx != context and ctx.alpha_equivalent(context):
                print("adapting request: {} ---> {}".format(context, ctx))
                for info in self.enumerate_with_info(ctx, size, pool):
                    yield info._replace(e=context.adapt(info.e, ctx))
                return
            # else:
            #     print("NOT adapting request: {} ---> {}".format(context, ctx))

        if context.parent() is not None:
            yield from self.enumerate_with_info(context.parent(), size, pool)

        # examples = context.instantiate_examples(self.examples)
        # print(examples)
        # k = self.key(examples, size, pool)
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
            for e in self.enumerate_core(context, size, pool):
                # print("considering {}".format(pprint(e)))

                fvs = free_vars(e)
                if not belongs_in_context(fvs, context):
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
                to_evict = []
                cost = self.cost_model.cost(e, pool)
                # print("prev={}".format(prev))
                # print("seen={}".format(self.seen))
                for ctx, prev_exp in prev:
                    prev_cost = self.cost_model.cost(prev_exp, pool)
                    ordering = cost.compare_to(prev_cost)
                    if ordering == Cost.BETTER:
                        if ctx == context:
                            # print("should evict {}".format(pprint(prev_exp)))
                            to_evict.append((ctx, prev_exp))
                    elif ordering == Cost.WORSE:
                        # print("should skip worse {}".format(pprint(e)))
                        assert not to_evict
                        should_keep = False
                        break
                    else:
                        # print("should skip equiv {}".format(pprint(e)))
                        assert not to_evict
                        assert ordering == Cost.UNORDERED
                        should_keep = False
                        break

                if to_evict:
                    for ctx, evicted_exp in to_evict:
                        print("EVICT {} FOR {}".format(pprint(evicted_exp, e)))
                    raise NotImplementedError()

                if should_keep:
                    seen_key = (context, pool, fp)
                    if seen_key not in self.seen:
                        self.seen[seen_key] = []
                    self.seen[seen_key].append(e)
                    info = EnumeratedExp(
                        e=e,
                        pool=pool,
                        size=size,
                        fingerprint=fp,
                        cost=None,
                        replaced=None,
                        replaced_size=None,
                        replaced_cost=None)
                    res.append(info)
                    yield info
            self.cache[k] = res
            # print("EXIT {}".format(k))
            self.in_progress.remove(k)

def build_candidates(cache : Cache, size : int, scopes : {EVar:(Exp,Pool)}, build_lambdas):
    if size == 0:
        for var, (_, pool) in scopes.items():
            yield (var, pool)
        for tup in LITERALS:
            yield tup

    for pool in ALL_POOLS:

        for e in cache.find_collections(pool=pool, size=size-1):
            yield (EEmptyList().with_type(e.type), pool)

        for e in cache.find(pool=pool, size=size-1):
            yield (ESingleton(e).with_type(TBag(e.type)), pool)

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
                t = a1.type
                if not is_numeric(t):
                    continue
                for a2 in cache.find(pool=pool, type=t, size=sz2):
                    yield (EBinOp(a1, "+", a2).with_type(t), pool)
                    yield (EBinOp(a1, "-", a2).with_type(t), pool)
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

class AuxBuilder(object):
    def __init__(self, wrapped):
        self.wrapped = wrapped
    def __call__(self, cache : Cache, size : int, scopes : {EVar:(Exp,Pool)}, build_lambdas):
        res = None
        gen = self.wrapped(cache, size, scopes, build_lambdas)
        while True:
            tup = gen.send(res)
            res = yield tup
            # print("$$   res={}".format(res))
            if res:
                yield from self.apply(cache, size, scopes, build_lambdas, *tup)
    def apply(self, cache, size, scopes, build_lambdas, e, pool):
        return
        yield

class MemoizedEnumerator(object):
    __slots__ = ("cache", "done", "iter")
    def __init__(self, *args, **kwargs):
        self.cache = []
        self.done = 0 # sizes [0 .. self.done] (inclusive) are complete
        self.iter = enumerate_exps(*args, **kwargs)
    def get(self, size):
        if size < 0:
            return ()
        if self.done <= size:
            for res in self.iter:
                if isinstance(res, StartMinorIteration):
                    while len(self.cache) <= res.size:
                        self.cache.append([])
                    self.done = res.size
                    if self.done > size:
                        break
                else:
                    assert res.size == self.done, "|res|={}, done={}".format(res.size, self.done)
                    self.cache[res.size].append(res)
        return self.cache[size]

def enumerate_exps(
        examples     : [{str:object}],
        cost_model   : CostModel,
        cost_ceiling : Cost = None,
        check_wf = None,
        build_candidates = build_candidates,
        scopes : { EVar : (Exp, Pool) } = None):

    """
    Enumerate expressions in order of size.  Expressions are deduplicated; an
    expression is only yielded if it is
        (1) new (it behaves differently on at least one example from every
            other expression yielded so far) or
        (2) better (it behaves identically to some other expression, but has
            lower cost)

    Yields StartMinorIteration and EnumeratedExp objects.
    """

    if scopes is None:
        scopes = {}
    depth = len(scopes)
    cache = Cache()
    seen = SeenSet()
    size = 0

    lbuilders = { }

    def build_lambdas(bag, pool, size):
        key = fingerprint(bag, examples)
        tup = lbuilders.get(key)
        if tup is None:
            v = fresh_var(bag.type.t)
            # TODO: inform the cost model about v's relationship to other
            # variables, i.e. EDeepIn(v, bag)
            new_examples = []
            for (ex, b) in zip(examples, eval_bulk(bag, examples)):
                for x in OrderedSet(b):
                    ex = dict(ex)
                    ex[v.id] = x
                    new_examples.append(ex)
            new_scopes = OrderedDict(scopes)
            new_scopes[v] = (bag, pool)
            builder = MemoizedEnumerator(
                new_examples,
                cost_model,
                cost_ceiling,
                check_wf=check_wf,
                build_candidates=build_candidates,
                scopes=new_scopes)
            lbuilders[key] = (v, builder)
        else:
            v, builder = tup
        for res in builder.get(size):
            if res.pool == pool:
                yield ELambda(v, res.e)

    while True:
        yield StartMinorIteration(size, len(cache))

        was_accepted = None
        it = build_candidates(cache, size, scopes, build_lambdas)
        while True:
            try:
                e, pool = it.send(was_accepted)
            except StopIteration:
                break

            _on_consider(depth, e, pool)
            if check_wf is not None:
                res = check_wf(e, pool)
                if not res:
                    _on_skip(depth, e, pool, "not well-formed [{}]".format(res.msg))
                    was_accepted = False
                    continue

            cost = cost_model.cost(e, pool)
            if pool == RUNTIME_POOL and use_cost_ceiling.value and cost_ceiling is not None and cost.compare_to(cost_ceiling) == Cost.WORSE:
                _on_skip(depth, e, pool, "worse than cost ceiling")
                was_accepted = False
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
                _on_accept(depth, e, pool, fp)
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
            was_accepted = should_add

        size += 1
