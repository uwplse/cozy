import itertools

from cozy.common import find_one, partition, pick_to_sum
from .core import ExpBuilder
from cozy.target_syntax import *
from cozy.syntax_tools import free_vars, break_conj, all_exps, replace, pprint, enumerate_fragments, mk_lambda, strip_EStateVar, alpha_equivalent, subst
from cozy.typecheck import is_numeric, is_collection
from cozy.pools import RUNTIME_POOL, STATE_POOL

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
    for (_, x, r, _) in enumerate_fragments(e):
        if isinstance(x, EBinOp) and x.op in ("+", "-"):
            # print("accel --> {}".format(pprint(r(x.e1))))
            yield from break_plus_minus(r(x.e1))
            # print("accel --> {}".format(pprint(r(x.e2))))
            yield from break_plus_minus(r(x.e2))
            if e.type == INT or is_collection(e.type):
                ee = EBinOp(r(x.e1), x.op, r(x.e2)).with_type(e.type)
                if e.type == INT and x.op == "-":
                    ee.op = "+"
                    ee.e2 = EUnaryOp("-", ee.e2).with_type(ee.e2.type)
                yield ee
            return
    yield e

def break_or(e):
    for (_, x, r, _) in enumerate_fragments(e):
        if isinstance(x, EBinOp) and x.op == BOp.Or:
            yield from break_or(r(x.e1))
            yield from break_or(r(x.e2))
            return
    yield e

def map_accelerate(e, state_vars, binders, args, cache, size):
    for (_, arg, f, bound) in enumerate_fragments(strip_EStateVar(e)):
        if any(v in state_vars for v in free_vars(arg)):
            continue
        for binder in (b for b in binders if b.type == arg.type and b not in bound):
            value = f(binder)
            if any(v not in state_vars and v not in binders for v in free_vars(value)):
                continue
            for bag in cache.find_collections(pool=STATE_POOL, size=size, of=arg.type):
                if isinstance(bag, EEmptyList):
                    continue
                m = EMakeMap2(bag,
                    ELambda(binder, value)).with_type(TMap(arg.type, e.type))
                assert not any(v in args for v in free_vars(m))
                if any(v in binders for v in free_vars(m)):
                    continue
                yield (m, STATE_POOL)
                yield (EMapGet(EStateVar(m).with_type(m.type), arg).with_type(e.type), RUNTIME_POOL)

def accelerate_filter(bag, p, state_vars, binders, args, cache, size):
    parts = list(break_conj(p.body))
    guards = []
    map_conds = []
    in_conds = []
    others = []
    for part in parts:
        if p.arg not in free_vars(part):
            others.append(part)
        elif all((v == p.arg or v in state_vars) for v in free_vars(part)):
            guards.append(part)
        elif infer_map_lookup(part, p.arg, state_vars):
            map_conds.append(part)
        elif isinstance(part, EBinOp) and part.op == BOp.In and all(v in state_vars for v in free_vars(part.e2)):
            in_conds.append(part)
        else:
            others.append(part)

    if in_conds:
        for i in range(len(in_conds)):
            rest = others + in_conds[:i] + in_conds[i+1:] + map_conds
            for tup in map_accelerate(
                    EFilter(EFilter(bag, ELambda(p.arg, EAll(guards))).with_type(bag.type), ELambda(p.arg, in_conds[i])).with_type(bag.type),
                    state_vars,
                    binders,
                    args,
                    cache,
                    size):
                (e, pool) = tup
                yield tup
                if e.type == bag.type and pool == RUNTIME_POOL:
                    yield (EFilter(e, ELambda(p.arg, EAll(rest))).with_type(bag.type), RUNTIME_POOL)

def break_bag(e):
    assert is_collection(e.type)
    if isinstance(e, EBinOp):
        if e.op == "+":
            yield from break_bag(e.e1)
            yield from break_bag(e.e2)
        else:
            assert e.op == "-"
            yield from break_bag(e.e1)
            for pos, x in break_bag(e.e2):
                yield (not pos, x)
    elif isinstance(e, EMap):
        for pos, x in break_bag(e.e):
            yield pos, EMap(x, e.f).with_type(e.type)
    elif isinstance(e, EFilter):
        for pos, x in break_bag(e.e):
            yield pos, EFilter(x, e.p).with_type(e.type)
    # elif isinstance(e, EStateVar):
    #     yield from break_bag(e.e)
    else:
        yield True, e

def break_sum(e):
    if not is_numeric(e.type):
        return
    if isinstance(e, EBinOp):
        if e.op == "+":
            yield from break_sum(e.e1)
            yield from break_sum(e.e2)
        else:
            assert e.op == "-"
            yield from break_sum(e.e1)
            for pos, x in break_sum(e.e2):
                yield (not pos, x)
    elif isinstance(e, EUnaryOp) and e.op == UOp.Sum:
        for pos, b in break_bag(e.e):
            yield pos, EUnaryOp(UOp.Sum, b).with_type(e.type)
    elif isinstance(e, EUnaryOp) and e.op == "-":
        for pos, x in break_sum(e.e):
            yield (not pos, x)
    # elif isinstance(e, EStateVar):
    #     yield from break_sum(e.e)
    else:
        yield True, e

def simplify_sum(e):
    parts = list(break_sum(e))
    t, f = partition(parts, lambda p: p[0])
    t = [x[1] for x in t]
    f = [x[1] for x in f]
    parts = []
    for x in t:
        opp = find_one(f, lambda y: alpha_equivalent(strip_EStateVar(x), strip_EStateVar(y)))
        if opp:
            f.remove(opp)
        else:
            parts.append(x)
    parts.extend(EUnaryOp("-", x).with_type(INT) for x in f)

    if not parts:
        return ZERO
    res = parts[0]
    for i in range(1, len(parts)):
        res = EBinOp(res, "+", parts[i]).with_type(INT)
    return res

class AcceleratedBuilder(ExpBuilder):

    def __init__(self, wrapped : ExpBuilder, binders : [EVar], state_vars : [EVar], args : [EVar]):
        super().__init__()
        self.wrapped = wrapped
        self.binders = binders
        self.state_vars = state_vars
        self.args = args

    def __repr__(self):
        return "AcceleratedBuilder(wrapped={!r}, binders={!r}, state_vars={!r}, args={!r})".format(
            self.wrapped,
            self.binders,
            self.state_vars,
            self.args)

    def check(self, e, pool):
        e._accel = True
        return super().check(e, pool)

    def build(self, cache, size):

        for e in cache.find(pool=RUNTIME_POOL, size=size-1, type=INT):
            e2 = simplify_sum(e)
            if e != e2:
                yield self.check(e2, RUNTIME_POOL)

        # Fixup EFilter(\x -> ECond...)
        for e in cache.find_collections(pool=RUNTIME_POOL, size=size-1):
            if isinstance(e, EFilter):
                for (_, x, r, _) in enumerate_fragments(e.p.body):
                    if isinstance(x, ECond):
                        lhs = EFilter(e.e, ELambda(e.p.arg, EAll([     x.cond , r(x.then_branch)]))).with_type(e.type)
                        rhs = EFilter(e.e, ELambda(e.p.arg, EAll([ENot(x.cond), r(x.else_branch)]))).with_type(e.type)
                        union = EBinOp(lhs, "+", rhs).with_type(e.type)
                        # yield self.check(lhs.p.body, RUNTIME_POOL)
                        # yield self.check(rhs.p.body, RUNTIME_POOL)
                        yield self.check(lhs, RUNTIME_POOL)
                        yield self.check(rhs, RUNTIME_POOL)
                        yield self.check(union, RUNTIME_POOL)

        # Try instantiating bound expressions
        for pool in (STATE_POOL, RUNTIME_POOL):
            for (sz1, sz2) in pick_to_sum(2, size-1):
                for e1 in cache.find(pool=pool, size=sz1):
                    for v in free_vars(e1):
                        if pool == RUNTIME_POOL:
                            e1 = subst(strip_EStateVar(e1), { sv.id : EStateVar(sv).with_type(sv.type) for sv in self.state_vars if sv != v })
                        for e2 in cache.find(pool=pool, type=v.type, size=sz2):
                            yield self.check(subst(e1, {v.id:e2}), pool)

        for (sz1, sz2) in pick_to_sum(2, size-1):
            for e in cache.find(pool=RUNTIME_POOL, size=sz1):
                for x, pool in map_accelerate(e, self.state_vars, self.binders, self.args, cache, sz2):
                    yield self.check(x, pool)
                if isinstance(e, EFilter) and not any(v in self.binders for v in free_vars(e)):
                    for x, pool in accelerate_filter(e.e, e.p, self.state_vars, self.binders, self.args, cache, sz2):
                        yield self.check(x, pool)

        for bag in cache.find_collections(pool=RUNTIME_POOL, size=size-1):
            for a in self.args:
                for v in self.state_vars:
                    if is_collection(v.type) and v.type == a.type:
                        v = EStateVar(v).with_type(v.type)
                        cond = EBinOp(a, BOp.In, v).with_type(BOOL)
                        yield self.check(EFilter(bag, mk_lambda(bag.type.t, lambda _:      cond )).with_type(bag.type), RUNTIME_POOL)
                        yield self.check(EFilter(bag, mk_lambda(bag.type.t, lambda _: ENot(cond))).with_type(bag.type), RUNTIME_POOL)

            if isinstance(bag, EFilter):
                if any(v not in self.state_vars for v in free_vars(bag.e)):
                    continue

                # separate filter conds
                const_parts, other_parts = partition(break_conj(bag.p.body), lambda e:
                    all((v == bag.p.arg or v in self.state_vars) for v in free_vars(e)))
                if const_parts and other_parts:
                    inner_filter = strip_EStateVar(EFilter(bag.e, ELambda(bag.p.arg, EAll(const_parts))).with_type(bag.type))
                    yield self.check(inner_filter, STATE_POOL)
                    outer_filter = EFilter(EStateVar(inner_filter).with_type(inner_filter.type), ELambda(bag.p.arg, EAll(other_parts))).with_type(bag.type)
                    yield self.check(outer_filter, RUNTIME_POOL)

                # construct map lookups
                binder = bag.p.arg
                inf = infer_map_lookup(bag.p.body, binder, set(self.state_vars))
                if inf:
                    key_proj, key_lookup, remaining_filter = inf
                    bag_binder = find_one(self.binders, lambda b: b.type == key_proj.type and b != binder)
                    if bag_binder:
                        m = strip_EStateVar(EMakeMap2(
                            EMap(bag.e, ELambda(binder, key_proj)).with_type(type(bag.type)(key_proj.type)),
                            ELambda(bag_binder, EFilter(bag.e, ELambda(binder, EEq(key_proj, bag_binder))).with_type(bag.type))).with_type(TMap(key_proj.type, bag.type)))
                        assert not any(v in self.args for v in free_vars(m))
                        yield self.check(m, STATE_POOL)
                        m = EStateVar(m).with_type(m.type)
                        mg = EMapGet(m, key_lookup).with_type(bag.type)
                        yield self.check(mg, RUNTIME_POOL)
                        yield self.check(EFilter(mg, ELambda(binder, remaining_filter)).with_type(mg.type), RUNTIME_POOL)

        # for e in cache.find(size=size-1):
        #     # F(xs +/- ys) ---> F(xs), F(ys)
        #     for z in break_plus_minus(e):
        #         if z != e:
        #             # print("broke {} --> {}".format(pprint(e), pprint(z)))
        #             yield z

        #     # try reordering operations
        #     for (_, e1, f) in enumerate_fragments(e):
        #         if e1.type == e.type and e1 != e:
        #             for (_, e2, g) in enumerate_fragments(e1):
        #                 if e2.type == e.type and e2 != e1:
        #                     # e == f(g(e2))
        #                     yield g(f(e2))

        yield from self.wrapped.build(cache, size)
