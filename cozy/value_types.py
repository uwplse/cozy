"""Python objects for representing values in Cozy's language.

Cozy's specification language includes several numeric types, lists, sets,
bags, maps, and more.  Values for some of these types (especially numbers) can
be represented using built-in Python types.  This module declares classes for
representing types that do not have a perfect correspondence to a built-in
Python type.  These classes all have a few important attributes:
 - these classes are immutable (and therefore hashable)
 - these collections can be compared with ==, <, <=, etc.
 - the collections have a deterministic iteration order
 - the iteration order for the collection affects equality and comparisons

Important types:
 - Map
 - Bag
 - Handle

Important functions:
 - cmp: compare two Cozy values
 - eq: determine whether two Cozy values are equal
"""

from collections import namedtuple
from functools import total_ordering

from cozy.syntax import (
    Type, THandle, INT, TEnum, TBag, TSet, TMap, TTuple, TList, TRecord)

@total_ordering
class Map(object):
    """A Cozy key-value map."""

    def __init__(self, type, default, items=()):
        self.type = type
        self.default = default
        self._items = []
        for (k, v) in items:
            self[k] = v
    def __setitem__(self, k, v):
        for i in range(len(self._items)):
            (kk, vv) = self._items[i]
            if eq(self.type.k, k, kk):
                self._items[i] = (kk, v)
                return
        self._items.append((k, v))
    def __getitem__(self, k):
        for i in range(len(self._items)):
            (kk, vv) = self._items[i]
            if eq(self.type.k, k, kk):
                return vv
        return self.default
    def items(self):
        yield from self._items
    def keys(self):
        for (k, v) in reversed(self._items):
            yield k
    def values(self):
        for (k, v) in self._items:
            yield v
    def _hashable(self):
        return (self.default,) + tuple(sorted(self._items))
    def __hash__(self):
        return hash(self._hashable())
    def __repr__(self):
        return "Map({}, {}, {})".format(repr(self.type), repr(self.default), repr(self._items))
    def __str__(self):
        return repr(self)
    def __lt__(self, other):
        return self._hashable() < other._hashable()
    def __eq__(self, other):
        return self._hashable() == other._hashable()

@total_ordering
class Bag(object):
    """A collection of Cozy values.

    This class serves to represent both sets and multisets; a set is just a
    Bag whose elements happen to be distinct."""

    def __init__(self, iterable=()):
        self.elems = iterable if isinstance(iterable, tuple) else tuple(iterable)
    def __hash__(self):
        return hash(self.elems)
    def __add__(self, other):
        return Bag(self.elems + other.elems)
    def __eq__(self, other):
        return self.elems == other.elems
    def __lt__(self, other):
        return self.elems < other.elems
    def __len__(self):
        return len(self.elems)
    def __getitem__(self, i):
        return self.elems[i]
    def __bool__(self):
        return bool(self.elems)
    def __str__(self):
        return repr(self)
    def __repr__(self):
        return "Bag({})".format(repr(self.elems))
    def __contains__(self, x):
        return x in self.elems
    def __iter__(self):
        return iter(self.elems)

Handle = namedtuple("Handle", ["address", "value"])

LT = -1
EQ =  0
GT =  1

def cmp(t : Type, v1, v2, deep : bool = False):
    stk = [(t, v1, v2)]

    orig_deep = deep
    def cleardeep():
        nonlocal deep
        deep = False
    def resetdeep():
        nonlocal deep
        deep = orig_deep

    while stk:
        head = stk.pop()
        if hasattr(head, "__call__"):
            head()
            continue
        (t, v1, v2) = head

        if isinstance(t, THandle):
            if deep:
                stk.append((t.value_type, v1.value, v2.value))
            stk.append((INT, v1.address, v2.address))
        elif isinstance(t, TEnum):
            i1 = t.cases.index(v1)
            i2 = t.cases.index(v2)
            if i1 == i2: continue
            if i1 <  i2: return LT
            else:        return GT
        elif isinstance(t, TBag) or isinstance(t, TSet):
            if deep:
                elems1 = list(v1)
                elems2 = list(v2)
            else:
                elems1 = list(sorted(v1))
                elems2 = list(sorted(v2))
            if len(elems1) < len(elems2): return LT
            if len(elems1) > len(elems2): return GT
            stk.extend(reversed([(t.t, x, y) for (x, y) in zip(elems1, elems2)]))
        elif isinstance(t, TMap):
            keys1 = Bag(v1.keys())
            keys2 = Bag(v2.keys())
            stk.extend(reversed([(t.v, v1[k], v2[k]) for k in sorted(keys1)]))
            stk.append(resetdeep)
            stk.append((TSet(t.k), keys1, keys2))
            stk.append(cleardeep)
            stk.append((t.v, v1.default, v2.default))
        elif isinstance(t, TTuple):
            stk.extend(reversed([(tt, vv1, vv2) for (tt, vv1, vv2) in zip(t.ts, v1, v2)]))
        elif isinstance(t, TList):
            stk.extend(reversed([(t.t, vv1, vv2) for (vv1, vv2) in zip(v1, v2)]))
            stk.append((INT, len(v1), len(v2)))
        elif isinstance(t, TRecord):
            stk.extend(reversed([(ft, v1[f], v2[f]) for (f, ft) in t.fields]))
        else:
            if   v1 == v2: continue
            elif v1 <  v2: return LT
            else:          return GT
    return EQ

def eq(t : Type, v1, v2):
    return cmp(t, v1, v2) == EQ
