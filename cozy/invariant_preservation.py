from itertools import chain

from cozy.target_syntax import *
from cozy.typecheck import is_collection
from cozy.solver import valid
from cozy.syntax_tools import pprint, subst, enumerate_fragments, cse, fresh_var, mk_lambda, shallow_copy
from cozy.incrementalization import delta_form
from cozy.opts import Option

invariant_preservation_check = Option("invariant-preservation-check", bool, True)

def true_of_all_reachable_handles(root : Exp, f, ty=None) -> Exp:
    """
    If f maps handle-type expressions to bool-type expressions, then
        true_of_all_reachable_handles(e, f)
    produces an expression that is true iff f(h) evaluates to true for every
    handle h reachable from e.

    The optional `ty` parameter allows you to filter to specific handle types.
    """
    if isinstance(root.type, THandle):
        return EAll((
            f(root) if (ty is None or root.type == ty) else T,
            true_of_all_reachable_handles(EGetField(root, "val").with_type(root.type.value_type), f, ty)))
    elif is_collection(root.type):
        return EUnaryOp(UOp.All,
            EMap(root, mk_lambda(root.type.t, lambda x: true_of_all_reachable_handles(x, f, ty))).with_type(type(root.type)(BOOL))).with_type(BOOL)
    elif isinstance(root.type, TTuple):
        return EAll(true_of_all_reachable_handles(ETupleGet(root, i).with_type(t), f, ty) for i, t in enumerate(root.type.ts))
    elif isinstance(root.type, TRecord):
        return EAll(true_of_all_reachable_handles(EGetField(root, f).with_type(t), f, ty) for f, t in root.type.fields)
    elif isinstance(root.type, TMap):
        # probably won't be hit since this pass runs just after parsing
        raise NotImplementedError()
    else:
        return T

def true_of_all_reachable_handles_at_method(spec : Spec, m : Method, f, ty=None):
    assert m in spec.methods
    return EAll(chain(
        (true_of_all_reachable_handles(EVar(v).with_type(t), f, ty) for v, t in spec.statevars),
        (true_of_all_reachable_handles(EVar(v).with_type(t), f, ty) for v, t in m.args)))

def add_implicit_handle_assumptions(spec : Spec):
    """
    At the start of every method, for all reachable handles (i.e. those stored
    on the data structure plus those in arguments):
        If two different handles have the same address, then they have the same
        value.
    """
    spec = shallow_copy(spec)
    new_methods = []
    for m in spec.methods:
        new_assumption = true_of_all_reachable_handles_at_method(spec, m, f=lambda h1:
            true_of_all_reachable_handles_at_method(spec, m, ty=h1.type, f=lambda h2:
                EImplies(EEq(h1, h2),
                    EEq(EGetField(h1, "val").with_type(h1.type.value_type),
                        EGetField(h2, "val").with_type(h2.type.value_type)))))
        # print("adding assumption to {}: {}".format(m.name, pprint(new_assumption)))
        m = shallow_copy(m)
        m.assumptions = list(m.assumptions) + [new_assumption]
        new_methods.append(m)
    spec.methods = new_methods
    return spec

def check_ops_preserve_invariants(spec : Spec):
    if not invariant_preservation_check.value:
        return []
    res = []
    for m in spec.methods:
        if not isinstance(m, Op):
            continue
        remap = delta_form(spec.statevars, m)
        # print(m.name)
        # for id, e in remap.items():
        #     print("  {id} ---> {e}".format(id=id, e=pprint(e)))
        for a in spec.assumptions:
            a_post_delta = subst(a, remap)
            assumptions = list(m.assumptions) + list(spec.assumptions)
            if not valid(cse(EImplies(EAll(assumptions), a_post_delta))):
                res.append("{.name!r} may not preserve invariant {}".format(m, pprint(a)))
    return res

def check_the_wf(spec : Spec):
    res = []
    for (a, e, r, bound) in enumerate_fragments(spec):
        if isinstance(e, EUnaryOp) and e.op == UOp.The:
            if not valid(cse(EImplies(EAll(a), EAny([EIsSingleton(e.e), EEmpty(e.e)])))):
                res.append("at {}: `the` is illegal since its argument may not be singleton".format(pprint(e)))
    return res
