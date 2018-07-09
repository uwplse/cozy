"""Well-formedness tests for Cozy expressions."""

from cozy.common import No, typechecked, OrderedSet
from cozy.target_syntax import *
from cozy.solver import ModelCachingSolver
from cozy.pools import RUNTIME_POOL, STATE_POOL
from cozy.structures import extension_handler
from cozy.contexts import Context, shred

class ExpIsNotWf(No):
    """An explanation for why an expression is not well-formed.

    This object is falsy so that it can be used elegantly in conditionals:

        if exp_wf(e, ...):
            <e is definitely well-formed>
    """
    def __init__(self, toplevel_expression, offending_subexpression, reason):
        super().__init__("at {}: {}".format(pprint(exc.offending_subexpression), exc.reason))
        self.toplevel_expression = toplevel_expression
        self.offending_subexpression = offending_subexpression
        self.reason = reason
    def __repr__(self):
        return "ExpIsNotWf({!r}, {!r}, {!r})".format(
            self.toplevel_expression,
            self.offending_subexpression,
            self.reason)

def exp_wf_nonrecursive(solver, e : Exp, context : Context, pool = RUNTIME_POOL, assumptions : Exp = T):
    state_vars = OrderedSet(v for v, p in context.vars() if p == STATE_POOL)
    args       = OrderedSet(v for v, p in context.vars() if p == RUNTIME_POOL)
    assumptions = EAll([assumptions, context.path_condition()])

    h = extension_handler(type(e))
    if h is not None:
        msg = h.check_wf(e, state_vars=state_vars, args=args, pool=pool, assumptions=assumptions, is_valid=solver.valid)
        if msg is not None:
            return No(msg)
        return True

    at_runtime = pool == RUNTIME_POOL
    if isinstance(e, EStateVar) and not at_runtime:
        return No("EStateVar in state pool position")
    if isinstance(e, EVar):
        if at_runtime and e in state_vars:
            return No("state var at runtime")
        elif not at_runtime and e in args:
            return No("arg in state exp")

    return True

@typechecked
def exp_wf(e : Exp, context : Context, pool = RUNTIME_POOL, assumptions : Exp = T, solver = None):
    """
    Returns True or an instance of ExpIsNotWf that indicates why `e` is not well-formed.
    """
    if solver is None:
        solver = ModelCachingSolver(vars=[], funcs={})
    for x, ctx, p in shred(e, context, pool):
        is_wf = exp_wf_nonrecursive(solver, x, ctx, p, assumptions=ctx.adapt(assumptions, context))
        if not is_wf:
            if isinstance(is_wf, No):
                return ExpIsNotWf(e, x, is_wf.msg)
            return is_wf
    return True
