import itertools

from cozy.common import typechecked, OrderedSet
from cozy.typecheck import is_collection, is_scalar
from cozy.target_syntax import *
from cozy.syntax_tools import pprint, free_vars
from cozy.solver import ModelCachingSolver
from cozy.pools import RUNTIME_POOL, STATE_POOL
from cozy.opts import Option
from cozy.structures import extension_handler
from cozy.contexts import Context, RootCtx, shred

allow_conditional_state = Option("allow-conditional-state", bool, True)
do_expensive_checks = Option("expensive-wf-checks", bool, True)

class ExpIsNotWf(Exception):
    def __init__(self, e, offending_subexpression, reason):
        super().__init__(reason)
        self.e = e
        self.offending_subexpression = offending_subexpression
        self.reason = reason

def exp_wf_nonrecursive(solver, e : Exp, context : Context, pool = RUNTIME_POOL, assumptions : Exp = T):
    state_vars = OrderedSet(v for v, p in context.vars() if p == STATE_POOL)
    args       = OrderedSet(v for v, p in context.vars() if p == RUNTIME_POOL)
    assumptions = EAll([assumptions, context.path_condition()])

    h = extension_handler(type(e))
    if h is not None:
        msg = h.check_wf(e, state_vars=state_vars, args=args, pool=pool, assumptions=assumptions, is_valid=solver.valid)
        if msg is not None:
            raise ExpIsNotWf(e, e, msg)
        return
    at_runtime = pool == RUNTIME_POOL
    if isinstance(e, EStateVar) and not at_runtime:
        raise ExpIsNotWf(e, e, "EStateVar in state pool position")
    if isinstance(e, EStateVar):
        fvs = free_vars(e.e)
        if not fvs:
            raise ExpIsNotWf(e, e, "constant value in state position")
        bad = [v for v in fvs if v not in state_vars]
        if bad:
            raise ExpIsNotWf(e, e, "free non-statevars in state position: {}".format(", ".join(v.id for v in bad)))
    if isinstance(e, EWithAlteredValue) and not at_runtime:
        raise ExpIsNotWf(e, e, "EWithAlteredValue in state position")
    if (isinstance(e, EDropFront) or isinstance(e, EDropBack)) and not at_runtime:
        raise ExpIsNotWf(e, e, "EDrop* in state position")
    if isinstance(e, EFlatMap) and not at_runtime:
        raise ExpIsNotWf(e, e, "EFlatMap in state position")
    if not at_runtime and isinstance(e, EBinOp) and e.type == INT:
        raise ExpIsNotWf(e, e, "integer arithmetic in state position")
    # if isinstance(e, EUnaryOp) and e.op == UOp.Distinct and not at_runtime:
    #     raise ExpIsNotWf(e, e, "'distinct' in state position")
    # if isinstance(e, EMapKeys) and not at_runtime:
    #     raise ExpIsNotWf(e, e, "'mapkeys' in state position")
    if isinstance(e, EVar):
        if at_runtime and e in state_vars:
            raise ExpIsNotWf(e, e, "state var at runtime")
        elif not at_runtime and e in args:
            raise ExpIsNotWf(e, e, "arg in state exp")
    # if is_collection(e.type) and is_collection(e.type.t):
    #     raise ExpIsNotWf(e, e, "collection of collection")
    if is_collection(e.type) and not is_scalar(e.type.t):
        raise ExpIsNotWf(e, e, "collection of nonscalar")
    if isinstance(e.type, TMap) and not is_scalar(e.type.k):
        raise ExpIsNotWf(e, e, "bad key type {}".format(pprint(e.type.k)))
    if isinstance(e.type, TMap) and isinstance(e.type.v, TMap):
        raise ExpIsNotWf(e, e, "map to map")
    # This check is probably a bad idea: whether `the` is legal may depend on
    # the contex that the expression is embedded within, so we can't skip it
    # during synthesis just because it looks invalid now.
    # if isinstance(e, EUnaryOp) and e.op == UOp.The:
    #     len = EUnaryOp(UOp.Length, e.e).with_type(INT)
    #     if not valid(EImplies(assumptions, EBinOp(len, "<=", ENum(1).with_type(INT)).with_type(BOOL))):
    #         raise ExpIsNotWf(e, e, "illegal application of 'the': could have >1 elems")
    if not at_runtime and isinstance(e, EBinOp) and e.op == "-" and is_collection(e.type):
        raise ExpIsNotWf(e, e, "collection subtraction in state position")
    if not at_runtime and isinstance(e, ESingleton):
        raise ExpIsNotWf(e, e, "singleton in state position")
    if not at_runtime and isinstance(e, ENum) and e.val != 0 and e.type == INT:
        raise ExpIsNotWf(e, e, "nonzero integer constant in state position")
    if not allow_conditional_state.value and not at_runtime and isinstance(e, ECond):
        raise ExpIsNotWf(e, e, "conditional in state position")
    if isinstance(e, EMakeMap2) and isinstance(e.e, EEmptyList):
        raise ExpIsNotWf(e, e, "trivially empty map")
    if do_expensive_checks.value and not at_runtime and isinstance(e, EFilter):
        # catch "peels": removal of zero or one elements
        if solver.valid(EImplies(assumptions, ELe(ELen(EFilter(e.e, ELambda(e.p.arg, ENot(e.p.body))).with_type(e.type)), ONE))):
            raise ExpIsNotWf(e, e, "filter is a peel")
    if do_expensive_checks.value and not at_runtime and isinstance(e, EMakeMap2) and is_collection(e.type.v):
        all_collections = [sv for sv in state_vars if is_collection(sv.type)]
        total_size = ENum(0).with_type(INT)
        for c in all_collections:
            total_size = EBinOp(total_size, "+", EUnaryOp(UOp.Length, c).with_type(INT)).with_type(INT)
        my_size = EUnaryOp(UOp.Length, EFlatMap(EUnaryOp(UOp.Distinct, e.e).with_type(e.e.type), e.value).with_type(e.type.v)).with_type(INT)
        s = EImplies(
            assumptions,
            EBinOp(total_size, ">=", my_size).with_type(BOOL))
        if not solver.valid(s):
            # from cozy.evaluation import eval
            # from cozy.solver import satisfy
            # model = satisfy(EAll([assumptions, EBinOp(total_size, "<", my_size).with_type(BOOL)]), collection_depth=3, validate_model=True)
            # assert model is not None
            # raise ExpIsNotWf(e, e, "non-polynomial-sized map ({}); total_size={}, this_size={}".format(model, eval(total_size, model), eval(my_size, model)))
            raise ExpIsNotWf(e, e, "non-polynomial-sized map")

@typechecked
def exp_wf(e : Exp, context : Context, pool = RUNTIME_POOL, assumptions : Exp = T, solver = None):
    """
    Returns True or throws exception indicating why `e` is not well-formed.
    """
    if solver is None:
        solver = ModelCachingSolver(vars=[], funcs={})
    for x, ctx, p in shred(e, context, pool):
        try:
            exp_wf_nonrecursive(solver, x, ctx, p, assumptions=ctx.adapt(assumptions, context))
        except ExpIsNotWf as exc:
            raise ExpIsNotWf(e, x, exc.reason)
    return True
