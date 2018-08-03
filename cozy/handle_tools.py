"""Utilities for working with "handles".

Handles (mutable heap-allocated objects) require careful treatment since
everything else in Cozy is relatively pure.  This module defines some useful
functions that operate on handles.
"""

from collections import OrderedDict

from cozy.common import typechecked
from cozy.target_syntax import *
from cozy.syntax_tools import fresh_var
from cozy.typecheck import is_collection

@typechecked
def _merge(a : {THandle:Exp}, b : {THandle:Exp}) -> {THandle:Exp}:
    """Merge the elements of `a` and `b`.

    If a key is present in both inputs, the output will have an expression
    computing the sum of the two entries for that key.

    NOTE: for efficiency, this procedure mutates and returns `a`.
    """
    res = a
    for k, vb in b.items():
        va = res.get(k)
        if va is None:
            res[k] = vb
        else:
            res[k] = EBinOp(va, "+", vb).with_type(va.type)
    return res

@typechecked
def reachable_handles_by_type(root : Exp) -> {THandle:Exp}:
    """
    Compute a mapping from handle types to bags of all handle objects of that
    type reachable from the given root.

    Note that the bags may contain duplicate handles.  This can happen in two
    ways:
     - there is a bag of handles reachable from the root that contains
       duplicate handles, or
     - the same handle is reachable from the root via two different paths
    """
    if isinstance(root.type, THandle):
        return _merge(
            { root.type : ESingleton(root).with_type(TBag(root.type)) },
            reachable_handles_by_type(EGetField(root, "val").with_type(root.type.value_type)))
    elif is_collection(root.type):
        v = fresh_var(root.type.elem_type)
        res = reachable_handles_by_type(v)
        for k, bag in list(res.items()):
            res[k] = EFlatMap(root, ELambda(v, bag)).with_type(bag.type)
        return res
    elif isinstance(root.type, TTuple):
        res = OrderedDict()
        for i, t in enumerate(root.type.ts):
            res = _merge(res, reachable_handles_by_type(ETupleGet(root, i).with_type(t)))
        return res
    elif isinstance(root.type, TRecord):
        res = OrderedDict()
        for f, t in root.type.fields:
            res = _merge(res, reachable_handles_by_type(EGetField(root, f).with_type(t)))
        return res
    elif isinstance(root.type, TMap):
        raise NotImplementedError()
    else:
        return OrderedDict()

@typechecked
def reachable_handles_at_method(spec : Spec, m : Method) -> {THandle:Exp}:
    """
    Compute a mapping from handle types to bags of all handle objects of that
    type reachable at entry to some method `m`.

    Note that the bags may contain duplicate handles.  See
    `reachble_handles_by_type` for information about how this can happen.
    """
    res = OrderedDict()
    for v, t in spec.statevars:
        res = _merge(res, reachable_handles_by_type(EVar(v).with_type(t)))
    for v, t in m.args:
        res = _merge(res, reachable_handles_by_type(EVar(v).with_type(t)))
    return res

@typechecked
def implicit_handle_assumptions(handles : {THandle:Exp}) -> [Exp]:
    """
    Compute a list of expressions that, in conjunction, assert that all handles
    in the values of the given dictionary satisfy:
     - any two handles with the same address have the same value

    For example:

        implicit_handle_assumptions(reachable_handles_at_method(spec, m))

    will produce expressions asserting that all handles reachable on entry to
    `m` satisfy the condition.
    """

    new_assumptions = []
    for t, bag in handles.items():
        new_assumptions.append(
            EForall(bag, lambda h1: EForall(bag, lambda h2:
                EImplies(EEq(h1, h2),
                    EEq(EGetField(h1, "val").with_type(h1.type.value_type),
                        EGetField(h2, "val").with_type(h2.type.value_type))))))
    return new_assumptions
