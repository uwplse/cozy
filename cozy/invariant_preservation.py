"""Functions for checking invariants and other properties of a Cozy spec."""

from cozy.common import typechecked
from cozy.target_syntax import *
from cozy.solver import valid
from cozy.syntax_tools import pprint, enumerate_fragments, shallow_copy, inline_calls, subst
from cozy.handle_tools import reachable_handles_at_method, implicit_handle_assumptions
from cozy.state_maintenance import mutate
from cozy.opts import Option

invariant_preservation_check = Option("invariant-preservation-check", bool, True)

@typechecked
def add_implicit_handle_assumptions(spec : Spec) -> Spec:
    """
    At the start of every method, for all reachable handles (i.e. those stored
    on the data structure plus those in arguments):
        If two different handles have the same address, then they have the same
        value.
    """
    spec = shallow_copy(spec)
    new_methods = []
    for m in spec.methods:
        handles = reachable_handles_at_method(spec, m)
        new_assumptions = implicit_handle_assumptions(handles)
        m = shallow_copy(m)
        m.assumptions = list(m.assumptions) + new_assumptions
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
        for a in spec.assumptions:
            print("Checking that {} preserves {}...".format(m.name, pprint(a)))
            a_post_delta = mutate(a, m.body)
            assumptions = list(m.assumptions) + list(spec.assumptions)
            if not valid(EImplies(EAll(assumptions), a_post_delta)):
                res.append("{.name!r} may not preserve invariant {}".format(m, pprint(a)))
    return res

def check_the_wf(spec : Spec):
    res = []
    for ctx in enumerate_fragments(spec):
        e = ctx.e
        if isinstance(e, EUnaryOp) and e.op == UOp.The:
            a = ctx.facts
            if not valid(EImplies(EAll(a), EAny([EIsSingleton(e.e), EEmpty(e.e)]))):
                res.append("at {}: `the` is illegal since its argument may not be singleton".format(pprint(e)))
    return res

def check_minmax_wf(spec : Spec):
    res = []
    for ctx in enumerate_fragments(spec):
        e = ctx.e
        if isinstance(e, EArgMin) or isinstance(e, EArgMax):
            a = ctx.facts
            if not valid(EImplies(EAll(a), EUnaryOp(UOp.Exists, e.e).with_type(BOOL))):
                res.append("at {}: result is ambiguous since {} could be empty".format(pprint(e), pprint(e.e)))
    return res

def check_calls_wf(spec : Spec):
    res = []
    queries = { m.name : m for m in spec.methods if isinstance(m, Query) }
    for ctx in enumerate_fragments(spec):
        e = ctx.e
        if isinstance(e, ECall):
            q = queries.get(e.func)
            if q is None:
                continue
            print("Checking call {}...".format(pprint(e)))
            a = EAll(ctx.facts)
            for precond in q.assumptions:
                precond = subst(precond, { v : val for (v, t), val in zip(q.args, e.args) })
                if not valid(inline_calls(spec, EImplies(a, precond))):
                    res.append("at {}: call may not satisfy precondition {}".format(pprint(e), pprint(precond)))
    return res
