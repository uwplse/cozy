import itertools

from .core import ExpBuilder
from cozy.target_syntax import *
from cozy.syntax_tools import mk_lambda, free_vars, break_conj

def _as_conjunction_of_equalities(p):
    if isinstance(p, EBinOp) and p.op == "and":
        return _as_conjunction_of_equalities(p.e1) + _as_conjunction_of_equalities(p.e2)
    elif isinstance(p, EBinOp) and p.op == "==":
        return [p]
    else:
        raise ValueError(p)

def as_conjunction_of_equalities(p):
    try:
        return _as_conjunction_of_equalities(p)
    except ValueError:
        return None

def infer_key_and_value(filter, binders, state : {EVar} = set()):
    equalities = as_conjunction_of_equalities(filter)
    if not equalities:
        return
    def can_serve_as_key(e, binder):
        fvs = free_vars(e)
        return binder in fvs and all(v == binder or v in state for v in fvs)
    def can_serve_as_value(e, binder):
        fvs = free_vars(e)
        return binder not in fvs and not all(v in state for v in fvs)
    for b in binders:
        sep = []
        for eq in equalities:
            if can_serve_as_key(eq.e1, b) and can_serve_as_value(eq.e2, b):
                sep.append((eq.e1, eq.e2))
            elif can_serve_as_key(eq.e2, b) and can_serve_as_value(eq.e1, b):
                sep.append((eq.e2, eq.e1))
        if len(sep) == len(equalities):
            key = ETuple(tuple(k for k, v in sep)).with_type(TTuple(tuple(k.type for k, v in sep))) if len(sep) > 1 else sep[0][0]
            val = ETuple(tuple(v for k, v in sep)).with_type(TTuple(tuple(v.type for k, v in sep))) if len(sep) > 1 else sep[0][1]
            yield b, key, val

def infer_map_lookup(filter, binder, state : {EVar}):
    map_conds = []
    other_conds = []
    for c in break_conj(filter):
        if list(infer_key_and_value(c, (binder,), state)):
            map_conds.append(c)
        else:
            other_conds.append(c)
    if map_conds:
        for (_, key_proj, key_lookup) in infer_key_and_value(EAll(map_conds), (binder,), state):
            return (key_proj, key_lookup, EAll(other_conds))
    else:
        return None
    assert False

class AcceleratedBuilder(ExpBuilder):
    def __init__(self, wrapped : ExpBuilder, binders : [EVar], state_vars : [EVar]):
        super().__init__()
        self.wrapped = wrapped
        self.binders = binders
        self.state_vars = state_vars
    def build(self, cache, size):
        yield from self.wrapped.build(cache, size)
        for bag in itertools.chain(cache.find(type=TBag, size=size-1), cache.find(type=TSet, size=size-1)):
            # construct map lookups
            if isinstance(bag, EFilter):
                binder = bag.p.arg
                inf = infer_map_lookup(bag.p.body, binder, set(self.state_vars))
                if inf:
                    key_proj, key_lookup, remaining_filter = inf

                    m = EMakeMap(
                        bag.e,
                        ELambda(binder, key_proj),
                        mk_lambda(bag.type, lambda xs: xs)).with_type(TMap(key_proj.type, bag.type))
                    yield m
                    mg = EMapGet(m, key_lookup).with_type(bag.type)
                    yield mg
                    yield EFilter(mg, ELambda(binder, remaining_filter)).with_type(mg.type)
