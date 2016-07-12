"""
The important method here is `implement`, which converts plans into
instances of AbstractImpl.
"""

import predicates
import plans
from structures.hash_map import make_key_args
from structures.vector_map import is_enumerable

class AbstractImpl(object):
    pass

class Iterable(AbstractImpl):
    pass

class BinarySearchable(AbstractImpl):
    def __init__(self, fields, predicate):
        self.fields = fields
        self.predicate = predicate

class SortedIterable(BinarySearchable):
    def __init__(self, fields, sortField, predicate):
        super(SortedIterable, self).__init__(fields, predicate)
        self.sortField = sortField

class Bucketed(AbstractImpl):
    def __init__(self, fields, qvars, predicate, value_impl):
        self.fields = fields
        self.qvars = qvars
        self.value_impl = value_impl

        key_fields = list(make_key_args(fields, predicate).keys())
        self.enum_p = []
        self.rest_p = []
        for cmp in predicates.break_conj(predicate):
            f = cmp.lhs if cmp.lhs.name in fields else cmp.rhs
            if is_enumerable(fields[f.name]):
                self.enum_p.append(cmp)
            else:
                self.rest_p.append(cmp)

class GuardedImpl(AbstractImpl):
    def __init__(self, predicate, fields, qvars, impl):
        self.predicate = predicate
        self.fields = fields
        self.qvars = qvars
        self.impl = impl

class Combine(AbstractImpl):
    def __init__(self, l, r):
        self.l = l
        self.r = r

class AbstractFilter(AbstractImpl):
    def __init__(self, t, fields, qvars, predicate):
        self.t = t
        self.fields = fields
        self.qvars = qvars
        self.predicate = predicate

def implement(plan, fields, qvars, resultTy):
    """
    Args:
        plan           - plans.Plan to implement
        fields         - dict { field_name : type }
        qvars          - dict { var_name   : type }
        resultTy       - an AbstractImpl
    Returns:
        an AbstractImpl
    """

    if type(plan) is plans.AllWhere:
        if plan.predicate == predicates.Bool(True):
            return resultTy
        else:
            return GuardedImpl(plan.predicate, fields, qvars, resultTy)
    elif type(plan) is plans.HashLookup:
        t = Bucketed(fields, qvars, plan.predicate, resultTy)
        return implement(plan.plan, fields, qvars, t)
    elif type(plan) is plans.BinarySearch:
        assert type(resultTy) in [Iterable, SortedIterable]
        if type(resultTy) is SortedIterable:
            return implement(plan.plan, fields, qvars, SortedIterable(fields, plan.sortField, plan.predicate))
        else:
            return implement(plan.plan, fields, qvars, BinarySearchable(fields, plan.predicate))
    elif type(plan) is plans.Concat:
        t1 = implement(plan.plan1, fields, qvars, resultTy)
        t2 = implement(plan.plan2, fields, qvars, resultTy)
        return Combine(t1, t2)
    elif type(plan) is plans.Filter:
        t = implement(plan.plan, fields, qvars, resultTy)
        return AbstractFilter(t, fields, qvars, plan.predicate)
    else:
        raise Exception("codegen not implemented for {}".format(type(plan)))
