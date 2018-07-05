"""
Handles (aka heap-allocated objects) require careful treatment since everything
else in Cozy is relatively pure.  This module defines some useful functions
that operate on handles.
"""

from collections import OrderedDict

from cozy.common import typechecked
from cozy.target_syntax import *
from cozy.syntax_tools import fresh_var, mk_lambda
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
    type reachable from the given root.

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

def EForall(e, p):
    return EUnaryOp(UOp.All, EMap(e, mk_lambda(e.type.t, p)).with_type(type(e.type)(BOOL))).with_type(BOOL)

@typechecked
def implicit_handle_assumptions_for_method(handles : {THandle:Exp}, m : Method) -> [Exp]:
    # for instance: implicit_handle_assumptions_for_method(reachable_handles_at_method(spec, m), m)
    new_assumptions = []
    for t, bag in handles.items():
        new_assumptions.append(
            EForall(bag, lambda h1: EForall(bag, lambda h2:
                EImplies(EEq(h1, h2),
                    EEq(EGetField(h1, "val").with_type(h1.type.value_type),
                        EGetField(h2, "val").with_type(h2.type.value_type))))))
    return new_assumptions
