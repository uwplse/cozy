
# All
# Distinct
# AnyElt
# Min
# Max
# Count
# Sum
# Empty

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
    def __init__(self, key_func, sub_agg):
        self.key_func = key_func
        self.sub_agg = sub_agg

class DistinctElements(Aggregation):
    pass
