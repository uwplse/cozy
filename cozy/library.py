"""
Concrete data structure implementations.
"""

from cozy.common import fresh_name, typechecked, product, cross_product
from cozy.target_syntax import *
from cozy.syntax_tools import equal, subst, fresh_var, pprint, shallow_copy
from cozy.evaluation import construct_value
from cozy.solver import valid

def cases(t):
    if t == BOOL:
        yield T
        yield F
    elif isinstance(t, TEnum):
        for c in t.cases:
            yield EEnumEntry(c).with_type(t)
    elif isinstance(t, TTuple):
        for entries in cross_product(cases(tt) for tt in t.ts):
            yield ETuple(tuple(entries)).with_type(t)
    else:
        raise ValueError(t)

def count_cases(t):
    return sum(1 for case in cases(t)) # less mem. than len(list(cases(t)))

def is_enumerable(t):
    try:
        count_cases(t)
        return True
    except ValueError:
        return False

class Library(object):
    @typechecked
    def impls(self, e : Exp, assumptions : Exp):
        ty = e.type
        if type(ty) is TMap:
            k = fresh_var(ty.k)
            for v in self.impls(EMapGet(e, k).with_type(e.type.v), assumptions):
                if is_enumerable(ty.k):
                    yield TVectorMap(ty.k, v)
                else:
                    yield TNativeMap(ty.k, v)
        elif type(ty) is TSet or (type(ty) is TBag and valid(EImplies(assumptions, EUnaryOp(UOp.AreUnique, e).with_type(BOOL)), model_callback=print)):
            if isinstance(ty.t, THandle):
                yield TIntrusiveLinkedList(ty.t)
            x = fresh_var(ty.t)
            for t in self.impls(x, EAll((assumptions, EIn(x, e)))):
                yield TNativeSet(t)
        elif type(ty) is TBag:
            x = fresh_var(ty.t)
            for t in self.impls(x, EAll((assumptions, EIn(x, e)))):
                yield TNativeList(t)
        elif type(ty) is TTuple:
            for refinements in cross_product([self.impls(ETupleGet(e, i).with_type(ty.ts[i]), assumptions) for i in range(len(ty.ts))]):
                yield TTuple(refinements)
        else:
            yield ty

class TNativeMap(TMap):
    def __init__(self, k, v):
        super().__init__(k, v)

class TVectorMap(TMap):
    def __init__(self, k, v):
        super().__init__(k, v)

    def rep_type(self):
        return TVector(self.v, count_cases(self.k))

    @property
    def all_keys(self) -> [Exp]:
        return cases(self.k)

    def to_index(self, key):
        if key.type == BOOL:
            return EBoolToInt(key).with_type(TInt())
        elif isinstance(key.type, TEnum):
            return EEnumToInt(key).with_type(TInt())
        elif isinstance(key.type, TTuple):
            i = self.to_index(ETupleGet(key, 0).with_type(key.type.ts[0]))
            for i in range(1, len(key.type.ts)):
                i = EBinOp(i, "*", ENum(count_cases(key.type.ts[i-1]))).with_type(TInt())
                i = EBinOp(i, "+", self.to_index(ETupleGet(key, i).with_type(key.type.ts[i]))).with_type(TInt())
        else:
            raise NotImplementedError(key.type)

    def construct_concrete(self, e : Exp, out : Exp):
        assert out.type == self, "{} : {}".format(pprint(e), pprint(e.type))
        out = shallow_copy(out).with_type(self.rep_type())
        assert isinstance(e, EMakeMap2) # TODO?
        k = fresh_var(self.k, "k")
        return seq(
            [SAssign(
                EVectorGet(out, ENum(i).with_type(INT)).with_type(self.v),
                construct_value(self.v))
                for (i, k) in enumerate(self.all_keys)] +
            [SForEach(k, e.e,
                SAssign(
                    EVectorGet(out, k).with_type(self.v),
                    ELet(k, e.value).with_type(self.v)))])

    @typechecked
    def update_key(self, m : Exp, k : Exp, v : EVar, change : Stm):
        idx = EVar(fresh_name("index")).with_type(TInt())
        return seq([
            SDecl(idx.id, self.to_index(k)),
            subst(change, {v.id : EVectorGet(m, idx)})])

    @typechecked
    def get_key(self, m : Exp, k : Exp):
        return EVectorGet(m, self.to_index(k))

class TIntrusiveLinkedList(TBag):
    def __init__(self, t):
        super().__init__(t)
        self.next_ptr = fresh_name("next_ptr")
        self.prev_ptr = fresh_name("prev_ptr")
        self.null = ENull().with_type(self.rep_type())

    def rep_type(self):
        return self.t

    def __eq__(self, other):
        return self is other
    def __hash__(self):
        return super().__hash__()
    def intrusive_data(self, handle_type):
        if handle_type == self.t:
            return [
                (self.next_ptr, self.t),
                (self.prev_ptr, self.t)]
        return []
    def implement_add(self, target, args):
        assert target.type == self
        target = shallow_copy(target).with_type(self.rep_type())
        new_elem, = args
        return seq([
            SAssign(EGetField(new_elem, self.next_ptr).with_type(self.t), target),
            SAssign(EGetField(new_elem, self.prev_ptr).with_type(self.t), self.null),
            SIf(ENot(equal(target, self.null)), SAssign(EGetField(target, self.prev_ptr).with_type(self.t), new_elem), SNoOp()),
            SAssign(target, new_elem)])
    def implement_remove(self, target, args):
        assert target.type == self
        target = shallow_copy(target).with_type(self.rep_type())
        elem, = args
        prev = EGetField(elem, self.prev_ptr).with_type(self.t)
        next = EGetField(elem, self.next_ptr).with_type(self.t)
        return seq([
            SIf(equal(elem, target), SAssign(target, next), SNoOp()),
            SIf(ENot(equal(prev, self.null)), SAssign(EGetField(prev, self.next_ptr).with_type(self.t), next), SNoOp()),
            SIf(ENot(equal(next, self.null)), SAssign(EGetField(next, self.prev_ptr).with_type(self.t), prev), SNoOp()),
            SAssign(next, self.null),
            SAssign(prev, self.null)])
    def for_each(self, id, iter, body):
        assert iter.type == self
        iter = shallow_copy(iter).with_type(self.rep_type())
        assert id.type == self.t
        next = fresh_name("next")
        return seq([
            SDecl(id.id, iter),
            SWhile(ENot(equal(id, self.null)),
                seq([
                    SDecl(next, EGetField(id, self.next_ptr).with_type(id.type)),
                    body,
                    SAssign(id, EVar(next).with_type(id.type))]))])
    def find_one(self, target):
        assert target.type == self
        target = shallow_copy(target).with_type(self.rep_type())
        return target
    def make_empty(self):
        return ENull().with_type(self)
    def construct_concrete(self, e : Exp, out : Exp):
        assert out.type == self, "{} : {}".format(pprint(e), pprint(e.type))
        out = shallow_copy(out).with_type(self.rep_type())
        x = fresh_var(self.t, "x")
        return seq([
            SAssign(out, self.null),
            SForEach(x, e, seq([
                SAssign(EGetField(x, self.next_ptr).with_type(self.t), out),
                SAssign(EGetField(x, self.prev_ptr).with_type(self.t), self.null),
                SIf(ENot(equal(out, self.null)), SAssign(EGetField(out, self.prev_ptr).with_type(self.t), x), SNoOp()),
                SAssign(out, x)]))])

class TNativeList(TBag):
    def __init__(self, t):
        super().__init__(t)

class TNativeSet(TSet):
    def __init__(self, t):
        super().__init__(t)
