
# All
# Distinct
# AnyElt
# Min
# Max
# Count
# Sum
# Empty

import syntax
from common import typechecked

class Aggregation(object):
    pass

class IterateOver(Aggregation):
    def __init__(self, projection):
        self.projection = projection

class Sum(Aggregation):
    def __init__(self, projection):
        self.projection = projection

class Min(Aggregation):
    def __init__(self, key_func):
        self.key_func = key_func

class Max(Aggregation):
    def __init__(self, key_func):
        self.key_func = key_func

class GroupBy(Aggregation):
    @typechecked
    def __init__(self, key_type : syntax.Type, key_func, sub_agg : Aggregation):
        self.key_type = key_type
        self.key_func = key_func
        self.sub_agg = sub_agg

class DistinctElements(Aggregation):
    pass

class AggSeq(Aggregation):
    """
    Applies self.agg1 to the collection, then self.agg2 to that result.
    """
    def __init__(self, agg1, agg2):
        self.agg1 = agg1
        self.agg2 = agg2

class Filter(Aggregation):
    def __init__(self, predicate):
        self.predicate = predicate
