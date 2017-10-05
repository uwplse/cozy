from cozy.syntax import *
from cozy.solver import valid
from cozy.syntax_tools import pprint, subst, enumerate_fragments, cse
from cozy.incrementalization import delta_form
from cozy.opts import Option

invariant_preservation_check = Option("invariant-preservation-check", bool, True)

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
