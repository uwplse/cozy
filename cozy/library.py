"""
Concrete data structure implementations.
"""

from cozy.common import fresh_name, typechecked, product, cross_product
from cozy.target_syntax import *
from cozy.syntax_tools import equal, subst, fresh_var

def count_cases(t):
    if t == BOOL:
        return 2
    elif isinstance(t, TEnum):
        return len(t.cases)
    elif isinstance(t, TTuple):
        return product(count_cases(tt) for tt in t.ts)
    elif isinstance(t, TRecord):
        return product(count_cases(tt) for (f, tt) in t.fields)
    else:
        raise ValueError(t)

def is_enumerable(t):
    try:
        count_cases(t)
        return True
    except ValueError:
        return False

class Library(object):
    def impls(self, ty):
        if type(ty) is TMap:
            for v in self.impls(ty.v):
                if is_enumerable(ty.k):
                    yield TVectorMap(ty.k, v)
                else:
                    yield TNativeMap(ty.k, v)
        elif type(ty) is TBag:
            for t in self.impls(ty.t):
                yield TNativeList(t)
        elif type(ty) is TSet:
            if isinstance(ty.t, THandle):
                yield TIntrusiveLinkedList(ty.t)
            for t in self.impls(ty.t):
                yield TNativeSet(t)
        elif type(ty) is TTuple:
            for refinements in cross_product([self.impls(t) for t in ty.ts]):
                yield TTuple(refinements)
        else:
            yield ty

NULL = ENull()

class TNativeMap(TMap):
    def __init__(self, k, v):
        super().__init__(k, v)

class TVectorMap(TMap):
    def __init__(self, k, v):
        super().__init__(k, v)

    def rep_type(self):
        return TVector(self.v, count_cases(self.k))

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
        assert target.type == self.rep_type()
        new_elem, = args
        return seq([
            SAssign(EGetField(new_elem, self.next_ptr).with_type(self.t), target),
            SAssign(EGetField(new_elem, self.prev_ptr).with_type(self.t), NULL),
            SIf(ENot(equal(target, NULL)), SAssign(EGetField(target, self.prev_ptr).with_type(self.t), new_elem), SNoOp()),
            SAssign(target, new_elem)])
    def implement_remove(self, target, args):
        assert target.type == self.rep_type()
        elem, = args
        prev = EGetField(elem, self.prev_ptr).with_type(self.t)
        next = EGetField(elem, self.next_ptr).with_type(self.t)
        return seq([
            SIf(equal(elem, target), SAssign(target, next), SNoOp()),
            SIf(ENot(equal(prev, NULL)), SAssign(EGetField(prev, self.next_ptr).with_type(self.t), next), SNoOp()),
            SIf(ENot(equal(next, NULL)), SAssign(EGetField(next, self.prev_ptr).with_type(self.t), prev), SNoOp()),
            SAssign(next, NULL),
            SAssign(prev, NULL)])
    def for_each(self, id, iter, body):
        assert iter.type == self.rep_type()
        assert id.type == self.t
        next = fresh_name("next")
        return seq([
            SDecl(id.id, iter),
            SWhile(ENot(equal(id, NULL)),
                seq([
                    SDecl(next, EGetField(id, self.next_ptr).with_type(id.type)),
                    body,
                    SAssign(id, EVar(next))]))])
    def find_one(self, target):
        assert target.type == self.rep_type()
        return target
    def make_empty(self):
        return ENull().with_type(self.t)
    def construct_concrete(self, e : Exp, out : Exp):
        assert out.type == self.rep_type()
        assert out.type == self.rep_type()
        x = fresh_var(self.t, "x")
        return seq([
            SAssign(out, NULL),
            SForEach(x, e, seq([
                SAssign(EGetField(x, self.next_ptr).with_type(self.t), out),
                SAssign(EGetField(x, self.prev_ptr).with_type(self.t), NULL),
                SIf(ENot(equal(out, NULL)), SAssign(EGetField(out, self.prev_ptr).with_type(self.t), x), SNoOp()),
                SAssign(out, x)]))])

class TNativeList(TBag):
    def __init__(self, t):
        super().__init__(t)

class TNativeSet(TSet):
    def __init__(self, t):
        super().__init__(t)
