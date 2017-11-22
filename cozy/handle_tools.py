"""
Handles (aka heap-allocated objects) require careful treatment since everything
else in Cozy is relatively pure.  This module defines some useful functions for
handling handles.
"""

from collections import OrderedDict

from cozy.common import typechecked
from cozy.syntax import Spec, Method, Exp, THandle, TTuple, TRecord, TMap, TBag, EVar, EBinOp, ESingleton, EGetField, ELambda, ETupleGet, EGetField
from cozy.target_syntax import EFlatMap
from cozy.syntax_tools import fresh_var
from cozy.typecheck import is_collection

@typechecked
def _merge(a : {THandle:Exp}, b : {THandle:Exp}) -> {THandle:Exp}:
    """NOTE: assumes ownership of `a`"""
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
    type reachable from the root given root.

    Note that the bags may contain duplicate handles.
    """
    if isinstance(root.type, THandle):
        return _merge(
            { root.type : ESingleton(root).with_type(TBag(root.type)) },
            reachable_handles_by_type(EGetField(root, "val").with_type(root.type.value_type)))
    elif is_collection(root.type):
        v = fresh_var(root.type.t)
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
    res = OrderedDict()
    for v, t in spec.statevars:
        res = _merge(res, reachable_handles_by_type(EVar(v).with_type(t)))
    for v, t in m.args:
        res = _merge(res, reachable_handles_by_type(EVar(v).with_type(t)))
    return res
