import math
import tempfile
import os
import subprocess

import plans
import predicates
from codegen_java import JavaCodeGenerator
from codegen_cpp import CppCodeGenerator

def _reduction(predicate):
    """Estimate of the factor by which the predicate reduces the space of entries"""
    f = 1.0
    for p in predicates.break_conj(predicate):
        if isinstance(p, predicates.Bool):
            if p.val:
                continue
            else:
                return 0
        elif isinstance(p, predicates.Compare) and p.op == predicates.Eq:
            f *= 0.2
        else:
            f *= 0.5
    return f

def _cost(plan, n=float(1000)):
    """Returns (cost,size) tuples"""
    if isinstance(plan, plans.AllWhere): return 1, n * _reduction(plan.predicate)
    if isinstance(plan, plans.HashLookup):
        cost1, size1 = _cost(plan.plan)
        return cost1 + 1, size1 * _reduction(plan.predicate)
    if isinstance(plan, plans.BinarySearch):
        cost1, size1 = _cost(plan.plan)
        return cost1 + (math.log(size1) if size1 >= 1 else 1) + 1, size1 * _reduction(plan.predicate)
    if isinstance(plan, plans.Filter):
        cost1, size1 = _cost(plan.plan)
        return cost1 + size1 + 1, size1 * _reduction(plan.predicate)
    if isinstance(plan, plans.Concat):
        cost1, size1 = _cost(plan.plan1)
        cost2, size2 = _cost(plan.plan2)
        return 1 + cost1 + cost2, size1 + size2
    raise Exception("Couldn't parse plan: {}".format(plan))

def cost(fields, qvars, plan):
    return _cost(plan)[0]
