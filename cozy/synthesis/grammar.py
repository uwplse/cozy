import itertools

from cozy.common import pick_to_sum, cross_product, group_by, find_one
from cozy.target_syntax import *
from cozy.syntax_tools import subst, mk_lambda, free_vars, is_scalar
from cozy.pools import STATE_POOL, RUNTIME_POOL
from .core import ExpBuilder

class BinderBuilder(ExpBuilder):
    def __init__(self, binders : [EVar], state_vars : [EVar]):
        super().__init__()
        self.binders = binders
        self.state_vars = state_vars
    def __repr__(self):
        return "BinderBuilder(binders={!r}, state_vars={!r})".format(
            self.binders,
            self.state_vars)
    def build(self, cache, size):
        # print("Cache:")
        # for (e, sz, pool) in cache:
        #     from cozy.syntax_tools import pprint
        #     print("    @size={}, pool={}\t:\t{}".format(sz, pool, pprint(e)))
        binders_by_type = group_by(self.binders, lambda b: b.type)

        for pool in (STATE_POOL, RUNTIME_POOL):
            if size == 1:
                yield (T, pool)
                yield (F, pool)
                yield (ENum(0).with_type(INT), pool)
                for b in self.binders:
                    yield (b, pool)
                for v in self.state_vars:
                    yield (v, pool)

            for t in list(cache.types()):
                if isinstance(t, TBag):
                    yield (EEmptyList().with_type(t), pool)
                    for e in cache.find(pool=pool, type=t.t, size=size-1):
                        yield (ESingleton(e).with_type(t), pool)

            for e in cache.find(pool=pool, type=TRecord, size=size-1):
                for (f,t) in e.type.fields:
                    yield (EGetField(e, f).with_type(t), pool)
            for e in cache.find(pool=pool, type=TBag(INT), size=size-1):
                yield (EUnaryOp(UOp.Sum, e).with_type(INT), pool)
            for e in cache.find(pool=pool, type=TBag, size=size-1):
                yield (EUnaryOp(UOp.The, e).with_type(TMaybe(e.type.t)), pool)
            for e in cache.find(pool=pool, type=THandle, size=size-1):
                yield (EGetField(e, "val").with_type(e.type.value_type), pool)
            for e in cache.find(pool=pool, type=TTuple, size=size-1):
                for n in range(len(e.type.ts)):
                    yield (ETupleGet(e, n).with_type(e.type.ts[n]), pool)
            for e in cache.find(pool=pool, type=BOOL, size=size-1):
                yield (EUnaryOp(UOp.Not, e).with_type(BOOL), pool)
            for e in cache.find(pool=pool, type=INT, size=size-1):
                yield (EUnaryOp("-", e).with_type(INT), pool)

            for (sz1, sz2) in pick_to_sum(2, size - 1):
                for a1 in cache.find(pool=pool, type=INT, size=sz1):
                    for a2 in cache.find(pool=pool, type=INT, size=sz2):
                        yield (EBinOp(a1, "+", a2).with_type(INT), pool)
                        yield (EBinOp(a1, ">", a2).with_type(BOOL), pool)
                        yield (EBinOp(a1, "<", a2).with_type(BOOL), pool)
                        yield (EBinOp(a1, ">=", a2).with_type(BOOL), pool)
                        yield (EBinOp(a1, "<=", a2).with_type(BOOL), pool)
                for a1 in cache.find(pool=pool, type=TBag, size=sz1):
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
                for m in cache.find(pool=pool, type=TMap, size=sz1):
                    for k in cache.find(pool=pool, type=m.type.k, size=sz2):
                        yield (EMapGet(m, k).with_type(m.type.v), pool)

            for bag in cache.find(pool=pool, type=TBag, size=size-1):
                # len of bag
                count = EUnaryOp(UOp.Sum, EMap(bag, mk_lambda(bag.type.t, lambda x: ENum(1).with_type(INT))).with_type(TBag(INT))).with_type(INT)
                yield (count, pool)
                # empty?
                yield (EUnaryOp(UOp.Empty, bag).with_type(BOOL), pool)
                # exists?
                yield (EUnaryOp(UOp.Exists, bag).with_type(BOOL), pool)
                # is-singleton?
                yield (EEq(count, ENum(1).with_type(INT)).with_type(BOOL), pool)

            for (sz1, sz2) in pick_to_sum(2, size - 1):
                for bag in cache.find(pool=pool, type=TBag, size=sz1):
                    for binder in binders_by_type[bag.type.t]:
                        for body in itertools.chain(cache.find(pool=pool, size=sz2), (binder,)):
                            # experimental filter
                            if binder not in free_vars(body):
                                continue
                            yield (EMap(bag, ELambda(binder, body)).with_type(TBag(body.type)), pool)
                            if body.type == BOOL:
                                yield (EFilter(bag, ELambda(binder, body)).with_type(bag.type), pool)
                            if pool == RUNTIME_POOL and isinstance(body.type, TBag):
                                yield (EFlatMap(bag, ELambda(binder, body)).with_type(TBag(body.type.t)), pool)

        for (sz1, sz2) in pick_to_sum(2, size - 1):
            for bag in cache.find(pool=STATE_POOL, type=TBag, size=sz1):
                if not is_scalar(bag.type.t):
                    continue
                for b in binders_by_type.get(bag.type.t, ()):
                    for val in cache.find(pool=STATE_POOL, size=sz2):
                        t = TMap(bag.type.t, val.type)
                        m = EMakeMap2(bag, ELambda(b, val)).with_type(t)
                        m._tag = True
                        yield (m, STATE_POOL)
