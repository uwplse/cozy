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

    def map_impls(self, impl, key_type, key_func, query_key_func):
        if is_enumerable(key_type):
            yield VectorMap(impl, key_type, key_func, query_key_func)
        else:
            yield HashMap(impl, key_type, key_func, query_key_func)

class Stored(object):
    def __init__(self, e):
        self.e = e
    def __str__(self):
        return "Stored({})".format(self.e)

class Filtered(object):
    def __init__(self, e, p):
        self.e = e
        self.p = e
    def __str__(self):
        return "Filtered({}, {})".format(self.e, self.p)
