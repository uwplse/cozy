import collections

import plans
import predicates
from common import fresh_name
import structures
from abstract_types import (
    Iterable,
    SortedIterable,
    BinarySearchable,
    Bucketed,
    GuardedImpl,
    Combine,
    AbstractFilter,
    implement)

################################################################################
# Part 2: Implementation

def enumerate_impls(fields, queries, extra_structures=None):
    """
    Code generation entry point.
      fields    - dict of {field_name : type}
      queries   - list of queries.Query objects with .bestPlans set
    Sets q.all_impls for each q in queries
    Returns an iterator of [ConcreteImpl] (one entry per query)
    """

    if extra_structures is None:
        extra_structures = lambda f: f

    @extra_structures
    def concretize(aimpl):
        if type(aimpl) is Iterable:
            yield structures.LinkedList()
            # yield structures.Array() # TODO
        elif type(aimpl) is SortedIterable:
            yield structures.AugTree(structures.interface.NativeTy(aimpl.fields[aimpl.sortField]), aimpl.sortField, aimpl.predicate, aimpl.fields)
            # yield structures.SortedArray(aimpl.field_type, aimpl.field_name) # TODO
        elif type(aimpl) is BinarySearchable:
            for sortField in aimpl.predicate.vars():
                sortField = sortField.name
                if sortField in fields:
                    yield structures.AugTree(structures.interface.NativeTy(fields[sortField]), sortField, aimpl.predicate, aimpl.fields)
                    # yield structures.SortedArray(aimpl.field_type, sortField, aimpl.field_name) # TODO
            for v in structures.VolumeTree.infer_volume(aimpl.fields, aimpl.predicate):
                yield structures.VolumeTree(v, aimpl.fields, aimpl.predicate, stack_iteration=False)
                yield structures.VolumeTree(v, aimpl.fields, aimpl.predicate, stack_iteration=True)
        elif type(aimpl) is Bucketed:
            for impl in concretize(aimpl.value_impl):
                if aimpl.enum_p and aimpl.rest_p:
                    m = structures.HashMap(aimpl.fields, predicates.conjunction(aimpl.rest_p), impl)
                    yield structures.VectorMap(aimpl.fields, predicates.conjunction(aimpl.enum_p), m)
                elif aimpl.enum_p:
                    yield structures.VectorMap(aimpl.fields, predicates.conjunction(aimpl.enum_p), impl)
                else: # aimpl.rest_p
                    yield structures.HashMap(aimpl.fields, predicates.conjunction(aimpl.rest_p), impl)
        elif type(aimpl) is GuardedImpl:
            for impl in concretize(aimpl.impl):
                yield structures.Guarded(impl, aimpl.fields, aimpl.qvars, aimpl.predicate)
        elif type(aimpl) is Combine:
            for impl1 in concretize(aimpl.l):
                for impl2 in concretize(aimpl.r):
                    yield structures.Tuple(impl1, impl2, aimpl.op)
        elif type(aimpl) is AbstractFilter:
            for impl in concretize(aimpl.t):
                yield structures.Filtered(impl, aimpl.fields, aimpl.qvars, aimpl.predicate)
        else:
            raise Exception("not sure how to concretize {}".format(aimpl))

    for q in queries:
        vars = collections.OrderedDict(q.vars)
        resultTy = Iterable() if q.sort_field is None else SortedIterable(fields, q.sort_field, predicates.Bool(True))
        all_impls = []
        for plan in q.bestPlans:
            all_impls += list(concretize(implement(plan, fields, vars, resultTy)))
        q.all_impls = all_impls
    return _enumerate_impls(fields, queries, 0, [None]*len(queries))

def _enumerate_impls(fields, queries, i, impls):
    if i >= len(queries):
        yield list(impls)
    else:
        for impl in queries[i].all_impls:
            impls[i] = impl
            for result in _enumerate_impls(fields, queries, i+1, impls):
                yield result
