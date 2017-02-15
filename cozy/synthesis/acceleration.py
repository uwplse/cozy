import itertools

from cozy.common import find_one
from .core import ExpBuilder
from cozy.target_syntax import *
from cozy.syntax_tools import free_vars, break_conj, all_exps, replace, pprint, enumerate_fragments
from cozy.desugar import desugar_exp
from cozy.typecheck import is_numeric

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

def can_serve_as_key(e, binder, state):
    fvs = free_vars(e)
    return binder in fvs and all(v == binder or v in state for v in fvs)

def can_serve_as_value(e, binder, state):
    fvs = free_vars(e)
    return binder not in fvs and not any(v == binder or v in state for v in fvs)

def infer_key_and_value(filter, binders, state : {EVar} = set()):
    equalities = as_conjunction_of_equalities(filter)
    if not equalities:
        return
    for b in binders:
        sep = []
        for eq in equalities:
            if can_serve_as_key(eq.e1, b, state) and can_serve_as_value(eq.e2, b, state):
                sep.append((eq.e1, eq.e2))
            elif can_serve_as_key(eq.e2, b, state) and can_serve_as_value(eq.e1, b, state):
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

def break_plus_minus(e):
    for (_, x, r) in enumerate_fragments(e):
        if isinstance(x, EBinOp) and x.op in ("+", "-"):
            # print("accel --> {}".format(pprint(r(x.e1))))
            yield from break_plus_minus(r(x.e1))
            # print("accel --> {}".format(pprint(r(x.e2))))
            yield from break_plus_minus(r(x.e2))
            if e.type == INT or isinstance(e.type, TBag):
                ee = EBinOp(r(x.e1), x.op, r(x.e2)).with_type(e.type)
                if e.type == INT and x.op == "-":
                    ee.op = "+"
                    ee.e2 = EUnaryOp("-", ee.e2).with_type(ee.e2.type)
                yield ee
            return
    yield e

class AcceleratedBuilder(ExpBuilder):

    def __init__(self, wrapped : ExpBuilder, binders : [EVar], state_vars : [EVar]):
        super().__init__()
        self.wrapped = wrapped
        self.binders = binders
        self.state_vars = state_vars

    def build(self, cache, size):

        for bag in itertools.chain(cache.find(type=TBag, size=size-1), cache.find(type=TSet, size=size-1)):
            # construct map lookups
            if isinstance(bag, EFilter):
                binder = bag.p.arg
                inf = infer_map_lookup(bag.p.body, binder, set(self.state_vars))
                if inf:
                    key_proj, key_lookup, remaining_filter = inf
                    bag_binder = find_one(self.binders, lambda b: b.type == bag.type)
                    if bag_binder:
                        m = EMakeMap(
                            bag.e,
                            ELambda(binder, key_proj),
                            ELambda(bag_binder, bag_binder)).with_type(TMap(key_proj.type, bag.type))
                        yield m
                        mg = EMapGet(m, key_lookup).with_type(bag.type)
                        yield mg
                        yield EFilter(mg, ELambda(binder, remaining_filter)).with_type(mg.type)

        for e in cache.find(size=size-1):
            # F(xs +/- ys) ---> F(xs), F(ys)
            for z in break_plus_minus(e):
                if z != e:
                    # print("broke {} --> {}".format(pprint(e), pprint(z)))
                    yield z

            # try reordering operations
            for (_, e1, f) in enumerate_fragments(e):
                if e1.type == e.type and e1 != e:
                    for (_, e2, g) in enumerate_fragments(e1):
                        if e2.type == e.type and e2 != e1:
                            # e == f(g(e2))
                            yield g(f(e2))

        yield from self.wrapped.build(cache, size)
