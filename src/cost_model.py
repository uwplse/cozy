
import math
import plans

def _cost(plan, n=float(1000)):
    """Returns (cost,size) tuples"""
    if isinstance(plan, plans.All): return 1, n
    if isinstance(plan, plans.Empty): return 1, 0
    if isinstance(plan, plans.HashLookup):
        cost1, size1 = _cost(plan.plan)
        return cost1 + 1, size1 / 2
    if isinstance(plan, plans.BinarySearch):
        cost1, size1 = _cost(plan.plan)
        return cost1 + (math.log(size1) if size1 >= 1 else 1), size1 / 2
    if isinstance(plan, plans.Filter):
        cost1, size1 = _cost(plan.plan)
        return cost1 + size1, size1 / 2
    if isinstance(plan, plans.Intersect):
        cost1, size1 = _cost(plan.plan1)
        cost2, size2 = _cost(plan.plan2)
        return cost1 + cost2 + size1 + size2, min(size1, size2) / 2
    if isinstance(plan, plans.Union):
        cost1, size1 = _cost(plan.plan1)
        cost2, size2 = _cost(plan.plan2)
        return cost1 + cost2 + size1 + size2, size1 + size2
    raise Exception("Couldn't parse plan: {}".format(plan))

def cost(plan):
    return _cost(plan)[0]
