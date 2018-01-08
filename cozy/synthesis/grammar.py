import itertools

from cozy.common import pick_to_sum, cross_product, group_by, find_one
from cozy.target_syntax import *
from cozy.syntax_tools import subst, mk_lambda, free_vars, is_scalar, pprint, strip_EStateVar
from cozy.typecheck import is_collection, is_numeric
from cozy.pools import STATE_POOL, RUNTIME_POOL, ALL_POOLS
from cozy.opts import Option

from .core import ExpBuilder

build_exprs = Option("build-exprs", bool, True)

class BinderBuilder(ExpBuilder):
    def __init__(self, binders : [EVar], state_vars : [EVar], args : [EVar] = []):
        super().__init__()
        self.binders = binders
        self.state_vars = state_vars
        self.args = args
    def __repr__(self):
        return "BinderBuilder(binders={!r}, state_vars={!r}, args={!r})".format(
            self.binders,
            self.state_vars,
            self.args)
    def build(self, cache, size):
        # print("Cache:")
        # for (e, sz, pool) in cache:
        #     from cozy.syntax_tools import pprint
        #     print("    @size={}, pool={}\t:\t{}".format(sz, pool, pprint(e)))
        binders_by_type = group_by(self.binders, lambda b: b.type)

        for pool in ALL_POOLS:
            if size == 1:
                yield self.check(T, pool)
                yield self.check(F, pool)
                yield self.check(ZERO, pool)
                yield self.check(ONE, pool)
                for b in self.binders:
                    yield self.check(b, pool)
                if pool == STATE_POOL:
                    for v in self.state_vars:
                        yield self.check(v, pool)
                elif pool == RUNTIME_POOL:
                    for v in self.args:
                        yield self.check(v, pool)

            if not build_exprs.value:
                return

            for e in cache.find(pool=STATE_POOL, size=size-1):
                yield self.check(EStateVar(e).with_type(e.type), RUNTIME_POOL)

            for e in cache.find(pool=pool, size=size-1):
                t = TBag(e.type)
                yield self.check(EEmptyList().with_type(t), pool)
                yield self.check(ESingleton(e).with_type(t), pool)

            for e in cache.find(pool=pool, type=TRecord, size=size-1):
                for (f,t) in e.type.fields:
                    yield self.check(EGetField(e, f).with_type(t), pool)
            for e in cache.find_collections(pool=pool, size=size-1):
                if is_numeric(e.type.t):
                    yield self.check(EUnaryOp(UOp.Sum, e).with_type(e.type.t), pool)
            for e in cache.find(pool=pool, type=THandle, size=size-1):
                yield self.check(EGetField(e, "val").with_type(e.type.value_type), pool)
            for e in cache.find(pool=pool, type=TTuple, size=size-1):
                for n in range(len(e.type.ts)):
                    yield self.check(ETupleGet(e, n).with_type(e.type.ts[n]), pool)
            for e in cache.find(pool=pool, type=BOOL, size=size-1):
                yield self.check(EUnaryOp(UOp.Not, e).with_type(BOOL), pool)
            for e in cache.find(pool=pool, type=INT, size=size-1):
                yield self.check(EUnaryOp("-", e).with_type(INT), pool)

            for m in cache.find(pool=pool, type=TMap, size=size-1):
                yield self.check(EMapKeys(m).with_type(TBag(m.type.k)), pool)

            for (sz1, sz2) in pick_to_sum(2, size - 1):
                for a1 in cache.find(pool=pool, size=sz1):
                    if not is_numeric(a1.type):
                        continue
                    for a2 in cache.find(pool=pool, type=a1.type, size=sz2):
                        yield self.check(EBinOp(a1, "+", a2).with_type(INT), pool)
                        yield self.check(EBinOp(a1, "-", a2).with_type(INT), pool)
                        yield self.check(EBinOp(a1, ">", a2).with_type(BOOL), pool)
                        yield self.check(EBinOp(a1, "<", a2).with_type(BOOL), pool)
                        yield self.check(EBinOp(a1, ">=", a2).with_type(BOOL), pool)
                        yield self.check(EBinOp(a1, "<=", a2).with_type(BOOL), pool)
                for a1 in cache.find_collections(pool=pool, size=sz1):
                    for a2 in cache.find(pool=pool, type=a1.type, size=sz2):
                        yield self.check(EBinOp(a1, "+", a2).with_type(a1.type), pool)
                        yield self.check(EBinOp(a1, "-", a2).with_type(a1.type), pool)
                    for a2 in cache.find(pool=pool, type=a1.type.t, size=sz2):
                        yield self.check(EBinOp(a2, BOp.In, a1).with_type(BOOL), pool)
                for a1 in cache.find(pool=pool, type=BOOL, size=sz1):
                    for a2 in cache.find(pool=pool, type=BOOL, size=sz2):
                        yield self.check(EBinOp(a1, BOp.And, a2).with_type(BOOL), pool)
                        yield self.check(EBinOp(a1, BOp.Or, a2).with_type(BOOL), pool)
                for a1 in cache.find(pool=pool, size=sz1):
                    if not isinstance(a1.type, TMap):
                        for a2 in cache.find(pool=pool, type=a1.type, size=sz2):
                            yield self.check(EEq(a1, a2), pool)
                for m in cache.find(pool=pool, type=TMap, size=sz1):
                    for k in cache.find(pool=pool, type=m.type.k, size=sz2):
                        yield self.check(EMapGet(m, k).with_type(m.type.v), pool)

            for (sz1, sz2, sz3) in pick_to_sum(3, size-1):
                for cond in cache.find(pool=pool, type=BOOL, size=sz1):
                    for then_branch in cache.find(pool=pool, size=sz2):
                        for else_branch in cache.find(pool=pool, size=sz3, type=then_branch.type):
                            yield self.check(ECond(cond, then_branch, else_branch).with_type(then_branch.type), pool)

            for bag in cache.find_collections(pool=pool, size=size-1):
                # len of bag
                count = EUnaryOp(UOp.Length, bag).with_type(INT)
                yield self.check(count, pool)
                # empty?
                yield self.check(EUnaryOp(UOp.Empty, bag).with_type(BOOL), pool)
                # exists?
                yield self.check(EUnaryOp(UOp.Exists, bag).with_type(BOOL), pool)
                # singleton?
                yield self.check(EEq(count, ONE), pool)

                yield self.check(EUnaryOp(UOp.The, bag).with_type(bag.type.t), pool)
                yield self.check(EUnaryOp(UOp.Distinct, bag).with_type(bag.type), pool)
                yield self.check(EUnaryOp(UOp.AreUnique, bag).with_type(BOOL), pool)

                if bag.type.t == BOOL:
                    yield self.check(EUnaryOp(UOp.Any, bag).with_type(BOOL), pool)
                    yield self.check(EUnaryOp(UOp.All, bag).with_type(BOOL), pool)

            for (sz1, sz2) in pick_to_sum(2, size - 1):
                for bag in cache.find_collections(pool=pool, size=sz1):
                    for binder in binders_by_type[bag.type.t]:
                        for body in itertools.chain(cache.find(pool=pool, size=sz2), (binder,)):
                            yield self.check(EMap(bag, ELambda(binder, body)).with_type(TBag(body.type)), pool)
                            if body.type == BOOL:
                                yield self.check(EFilter(bag, ELambda(binder, body)).with_type(bag.type), pool)
                            if body.type == INT:
                                yield self.check(EArgMin(bag, ELambda(binder, body)).with_type(bag.type.t), pool)
                                yield self.check(EArgMax(bag, ELambda(binder, body)).with_type(bag.type.t), pool)
                            if pool == RUNTIME_POOL and isinstance(body.type, TBag):
                                yield self.check(EFlatMap(bag, ELambda(binder, body)).with_type(TBag(body.type.t)), pool)

        for (sz1, sz2) in pick_to_sum(2, size - 1):
            for bag in cache.find_collections(pool=STATE_POOL, size=sz1):
                if not is_scalar(bag.type.t):
                    continue
                for b in binders_by_type[bag.type.t]:
                    for val in cache.find(pool=STATE_POOL, size=sz2):
                        t = TMap(bag.type.t, val.type)
                        m = EMakeMap2(bag, ELambda(b, val)).with_type(t)
                        yield self.check(m, STATE_POOL)
