from cozy.syntax import *
from cozy.solver import valid
from cozy.syntax_tools import pprint
from cozy.incrementalization import to_delta, derivative, apply_delta
from cozy.opts import Option

invariant_preservation_check = Option("invariant-preservation-check", bool, True)

def check_ops_preserve_invariants(spec : Spec):
    if not invariant_preservation_check.value:
        return []
    res = []
    for m in spec.methods:
        if not isinstance(m, Op):
            continue
        var, delta = to_delta(spec.statevars, m)
        for a in spec.assumptions:
            deriv, _ = derivative(a, var, delta, [], [])
            a_post_delta = apply_delta(a, deriv)
            assumptions = list(m.assumptions) + list(spec.assumptions)
            if not valid(EImplies(EAll(assumptions), a_post_delta)):
                res.append("{.name!r} may not preserve invariant {}".format(m, pprint(a)))
    return res
