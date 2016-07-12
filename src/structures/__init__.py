"""
Various data structures Cozy knows how to use.
"""

from . import interface
from .filtered         import Filtered
from .guarded          import Guarded
from .linked_list      import LinkedList
from .array_list       import ArrayList
from .hash_map         import HashMap
from .vector_map       import VectorMap
from .cozy_hash_map    import CozyHashMap
from .aug_tree         import AugTree
from .volume_tree      import VolumeTree
from .combined         import Tuple
from .hamt             import Hamt
from .tracked_sum      import TrackedSum

class Library(object):

    def __init__(self):
        self.enable_arrays = False
        self.enable_volume_trees = False

    def bag_impls(self, collection):
        yield LinkedList(collection)
        if self.enable_arrays:
            yield ArrayList(collection)

    def sum_impls(self, collection):
        yield TrackedSum(collection)
        # elif isinstance(agg, aggregations.Min):
        #     yield TrackedMin(collection, agg.key_func)
        #     yield MinHeap(collection, agg.key_func)
        # elif isinstance(agg, aggregations.Max):
        #     yield TrackedMax(collection, agg.key_func)
        #     yield MaxHeap(collection, agg.key_func)
        # elif isinstance(agg, aggregations.DistinctElements):
        #     yield HashSet(collection, agg.key_func)

    def map_impls(self, impl, key_type, key_func, query_key_func):
        if is_enumerable(key_type):
            yield VectorMap(impl, key_type, key_func, query_key_func)
        else:
            yield HashMap(impl, key_type, key_func, query_key_func)
