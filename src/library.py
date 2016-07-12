"""
Concrete data structure implementations.
"""

import syntax
import syntax_tools
import aggregations

# class ConcreteType(syntax.Type):
#     def prettyprint(self):
#         raise NotImplementedError(str(type(self)))

# class LinkedList(ConcreteType):
#     def __init__(self, t):
#         self.t = t
#     def prettyprint(self):
#         return "LinkedList<{}>".format(syntax_tools.pprint(self.t))

# class ArrayList(ConcreteType):
#     pass

# class HashMap(ConcreteType):
#     def __init__(self, key_type, value_type):
#         self.k = key_type
#         self.v = value_type
#     def prettyprint(self):
#         return "HashMap<{}, {}>".format(syntax_tools.pprint(self.k), syntax_tools.pprint(self.v))

# class AugTree(ConcreteType):
#     pass

# class Heap(ConcreteType):
#     pass

# class TrackedSum(ConcreteType):
#     pass

# class TrackedMinOrMax(ConcreteType):
#     pass

class TPtr(syntax.Type):
    def __init__(self, t):
        self.t = t

class TArray(syntax.Type):
    def __init__(self, t):
        self.t = t

class TVector(syntax.Type):
    def __init__(self, t, size):
        self.t = t
        self.size = size

class ConcreteImpl(object):

    def rep(self, handle_type : syntax.Type) -> syntax.Type:
        raise NotImplementedError(str(type(self)))

    def handle_rep(self, handle_type : syntax.Type) -> syntax.Type:
        raise NotImplementedError(str(type(self)))

    def exec_query(self, data, vars) -> syntax.Exp:
        raise NotImplementedError(str(type(self)))

    def update(self, data, var, delta) -> ([Goal], syntax.Stm):
        raise NotImplementedError(str(type(self)))

class LinkedList(ConcreteImpl):
    def __init__(self):
        pass
    def rep(self, handle_type):
        return TPtr(handle_type)
    def handle_rep(self, handle_type):
        return syntax.TRecord([
            "next": TPtr(handle_type),
            "prev": TPtr(handle_type)])
    def exec_query(self, data, vars):

class Library(object):

    def basic_impls(self, agg, collection):
        if isinstance(agg, aggregations.IterateOver):
            yield LinkedList(collection)
            yield ArrayList(collection)
        elif isinstance(agg, aggregations.Sum):
            yield TrackedSum(collection)
        elif isinstance(agg, aggregations.Min):
            yield TrackedMin(collection, agg.key_func)
            yield MinHeap(collection, agg.key_func)
        elif isinstance(agg, aggregations.Max):
            yield TrackedMax(collection, agg.key_func)
            yield MaxHeap(collection, agg.key_func)
        elif isinstance(agg, aggregations.DistinctElements):
            yield HashSet(collection, agg.key_func)

    def map_impls(self, sub_impl, key_type, key_func, query_key_func):
        yield HashMap(sub_impl, key_type, key_func, query_key_func)
