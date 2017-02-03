import itertools

from cozy.common import pick_to_sum, cross_product, group_by
from cozy.target_syntax import *
from cozy.syntax_tools import subst, mk_lambda, free_vars, is_scalar
from .core import ExpBuilder

class BinderBuilder(ExpBuilder):
    def __init__(self, binders : [EVar], state_vars : [EVar]):
        super().__init__()
        self.binders = binders
        self.state_vars = state_vars
    def build(self, cache, size):
        # print("Cache:")
        # for (e, sz) in cache:
        #     from cozy.syntax_tools import pprint
        #     print("    @{}\t:\t{}".format(sz, pprint(e)))
        if size == 1:
            yield T
            yield F
            yield ENum(0).with_type(INT)
            yield from self.binders

        for t in list(cache.types()):
            if isinstance(t, TBag):
                yield EEmptyList().with_type(t)
                for e in cache.find(type=t.t, size=size-1):
                    yield ESingleton(e).with_type(t)

        for e in cache.find(type=TRecord, size=size-1):
            for (f,t) in e.type.fields:
                yield EGetField(e, f).with_type(t)
        for e in itertools.chain(cache.find(type=TBag(INT), size=size-1), cache.find(type=TSet(INT), size=size-1)):
            yield EUnaryOp("sum", e).with_type(INT)
        for e in cache.find(type=TBag, size=size-1):
            yield EUnaryOp("the", e).with_type(TMaybe(e.type.t))
        for e in cache.find(type=THandle, size=size-1):
            yield EGetField(e, "val").with_type(e.type.value_type)
        for e in cache.find(type=TTuple, size=size-1):
            for n in range(len(e.type.ts)):
                yield ETupleGet(e, n).with_type(e.type.ts[n])
        for e in cache.find(type=BOOL, size=size-1):
            yield EUnaryOp("not", e).with_type(BOOL)
        for e in cache.find(type=INT, size=size-1):
            yield EUnaryOp("-", e).with_type(INT)

        for (sz1, sz2) in pick_to_sum(2, size - 1):
            # Try instantiating bound expressions
            for e1 in cache.find(size=sz1):
                binders = free_vars(e1) & set(self.binders)
                for b in binders:
                    for e2 in cache.find(type=b.type, size=sz2):
                        e = subst(e1, { b.id: e2 })
                        e._tag = True
                        yield e
            for a1 in cache.find(type=INT, size=sz1):
                for a2 in cache.find(type=INT, size=sz2):
                    # yield EBinOp(a1, "+", a2).with_type(INT)
                    # yield EBinOp(a1, "-", a2).with_type(INT)
                    yield EBinOp(a1, ">", a2).with_type(BOOL)
                    yield EBinOp(a1, "<", a2).with_type(BOOL)
                    yield EBinOp(a1, ">=", a2).with_type(BOOL)
                    yield EBinOp(a1, "<=", a2).with_type(BOOL)
            for a1 in cache.find(type=TBag, size=sz1):
                for a2 in cache.find(type=a1.type, size=sz2):
                    yield EBinOp(a1, "+", a2).with_type(a1.type)
            for a1 in cache.find(type=BOOL, size=sz1):
                for a2 in cache.find(type=BOOL, size=sz2):
                    yield EBinOp(a1, "and", a2).with_type(BOOL)
                    yield EBinOp(a1, "or", a2).with_type(BOOL)
            for a1 in cache.find(size=sz1):
                if not isinstance(a1.type, TMap):
                    for a2 in cache.find(type=a1.type, size=sz2):
                        yield EBinOp(a1, "==", a2).with_type(BOOL)
            for m in cache.find(type=TMap, size=sz1):
                for k in cache.find(type=m.type.k, size=sz2):
                    yield EMapGet(m, k).with_type(m.type.v)

        for bag in itertools.chain(cache.find(type=TBag, size=size-1), cache.find(type=TSet, size=size-1)):
            # len of bag
            count = EUnaryOp("sum", EMap(bag, mk_lambda(bag.type.t, lambda x: ENum(1).with_type(INT))).with_type(TBag(INT))).with_type(INT)
            yield count
            # empty?
            empty = EBinOp(count, "==", ENum(0).with_type(INT)).with_type(BOOL)
            yield empty
            # exists?
            yield ENot(empty)

        binders_by_type = group_by(self.binders, lambda b: b.type)
        for (sz1, sz2, sz3) in pick_to_sum(3, size - 1):
            for bag in itertools.chain(cache.find(type=TBag, size=sz1), cache.find(type=TSet, size=sz1)):
                if not all((v in self.binders or v in self.state_vars) for v in free_vars(bag)):
                    continue
                for k in cache.find(size=sz2):
                    if not is_scalar(k.type):
                        continue
                    kfvs = free_vars(k)
                    if not all((v in self.binders or v in self.state_vars) for v in kfvs):
                        continue
                    for val in cache.find(size=sz3):
                        valfvs = free_vars(val)
                        if not all((v in self.binders or v in self.state_vars) for v in valfvs):
                            continue
                        for (b1, b2) in cross_product([binders_by_type[bag.type.t], binders_by_type[bag.type]]):
                            if not (b1 in kfvs and b2 in valfvs):
                                continue
                            yield EMakeMap(bag, ELambda(b1, k), ELambda(b2, val)).with_type(TMap(k.type, val.type))

        for (sz1, sz2) in pick_to_sum(2, size - 1):
            for bag in itertools.chain(cache.find(type=TBag, size=sz1), cache.find(type=TSet, size=sz1)):
                for binder in binders_by_type[bag.type.t]:
                    for body in cache.find(size=sz2):
                        # experimental filter
                        if binder not in free_vars(body):
                            continue
                        yield EMap(bag, ELambda(binder, body)).with_type(TBag(body.type))
                        if body.type == BOOL:
                            yield EFilter(bag, ELambda(binder, body)).with_type(bag.type)
                        if isinstance(body.type, TBag):
                            yield EFlatMap(bag, ELambda(binder, body)).with_type(TBag(body.type.t))
