"""
Concrete data structure implementations.
"""

from common import fresh_name
from target_syntax import *
from syntax_tools import equal

class Library(object):
    def impls(self, ty):
        if type(ty) is TMap:
            for k in self.impls(ty.k):
                for v in self.impls(ty.v):
                    yield TNativeMap(k, v)
        elif type(ty) is TBag:
            for t in self.impls(ty.t):
                if isinstance(ty.t, THandle):
                    yield TIntrusiveLinkedList(ty.t)
                yield TLinkedList(ty.t)
                yield TArrayList(ty.t)
        else:
            yield ty

NULL = ENull()

class TNativeMap(TMap):
    def __init__(self, k, v):
        super().__init__(k, v)

class TIntrusiveLinkedList(TBag):
    def __init__(self, t):
        super().__init__(t)
        self.next_ptr = fresh_name("next_ptr")
        self.prev_ptr = fresh_name("prev_ptr")
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
        new_elem, = args
        return seq([
            SAssign(EGetField(new_elem, self.next_ptr).with_type(self.t), target),
            SAssign(EGetField(new_elem, self.prev_ptr).with_type(self.t), NULL),
            SIf(ENot(equal(target, NULL)), SAssign(EGetField(target, self.prev_ptr).with_type(self.t), new_elem), SNoOp()),
            SAssign(target, new_elem)])
    def implement_remove(self, target, args):
        elem, = args
        prev = EGetField(elem, self.prev_ptr).with_type(self.t)
        next = EGetField(elem, self.next_ptr).with_type(self.t)
        return seq([
            SIf(equal(elem, target), SAssign(target, next), SNoOp()),
            SIf(ENot(equal(prev, NULL)), SAssign(EGetField(prev, self.next_ptr).with_type(self.t), next), SNoOp()),
            SIf(ENot(equal(next, NULL)), SAssign(EGetField(next, self.prev_ptr).with_type(self.t), prev), SNoOp()),
            SAssign(next, NULL),
            SAssign(prev, NULL)])

class TLinkedList(TBag):
    def __init__(self, t):
        super().__init__(t)

class TArrayList(TBag):
    def __init__(self, t):
        super().__init__(t)
