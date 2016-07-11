"""
Concrete data structure implementations.
"""
import syntax

class ConcreteType(syntax.Type):
    pass

class LinkedList(ConcreteType):
    def __init__(self, t):
        self.t = t

class ArrayList(ConcreteType):
    pass

class HashMap(ConcreteType):
    def __init__(self, key_type, value_type):
        self.k = key_type
        self.v = value_type

class AugTree(ConcreteType):
    pass

class Heap(ConcreteType):
    pass

class TrackedSum(ConcreteType):
    pass

class TrackedMinOrMax(ConcreteType):
    pass
