import itertools

from cozy.common import find_one, partition, pick_to_sum, unique
from cozy.target_syntax import *
from cozy.syntax_tools import fresh_var, free_vars, break_conj, pprint, enumerate_fragments, mk_lambda, strip_EStateVar, alpha_equivalent, subst, break_sum, replace, compose
from cozy.typecheck import is_numeric, is_collection
from cozy.pools import RUNTIME_POOL, STATE_POOL, ALL_POOLS, pool_name
from cozy.simplification import simplify
from cozy.structures.heaps import TMinHeap, TMaxHeap, EMakeMinHeap, EMakeMaxHeap, EHeapPeek, EHeapPeek2
from cozy.evaluation import construct_value

accelerate = Option("acceleration-rules", bool, True)

def EUnion(es):
    es = [e for x in es for e in break_sum(x) if e != EEmptyList()]
    if not es:
        return EEmptyList()
    return build_balanced_tree(es[0].type, "+", es)

def MkFlatMap(bag, f):
    if isinstance(f.body, ESingleton):
        return EMap(bag, ELambda(f.arg, f.body.e)).with_type(f.body.type)
    if isinstance(f.body, EEmptyList):
        return f.body
    return EFlatMap(bag, f).with_type(f.body.type)

@typechecked
def reachable_values_of_type(root : Exp, t : Type) -> Exp:
    """
    Find all values of the given type reachable from the given root.
    """
    if root.type == t:
        return ESingleton(root).with_type(TBag(t))
    elif is_collection(root.type):
        v = fresh_var(root.type.t)
        res = reachable_values_of_type(v, t)
        return MkFlatMap(root, ELambda(v, res))
    elif isinstance(root.type, THandle):
        return reachable_values_of_type(EGetField(root, "val").with_type(root.type.value_type), t)
    elif isinstance(root.type, TTuple):
        sub = [reachable_values_of_type(ETupleGet(root, i).with_type(tt), t) for (i, tt) in enumerate(root.type.ts)]
        return EUnion(sub).with_type(TBag(t))
    elif isinstance(root.type, TRecord):
        sub = [reachable_values_of_type(EGetField(root, f).with_type(ft), t) for (f, ft) in root.type.fields]
        return EUnion(sub).with_type(TBag(t))
    elif isinstance(root.type, TMap):
        raise NotImplementedError()
    else:
        return EEmptyList().with_type(TBag(t))

def map_accelerate(e, state_vars, args, cache, size):
    for ctx in enumerate_fragments(e):
        if ctx.pool != RUNTIME_POOL:
            continue
        arg = ctx.e
        if any(v in ctx.bound_vars for v in free_vars(arg)):
            continue
        binder = fresh_var(arg.type)
        # value = ctx.replace_e_with(binder)
        # print("{} ? {}".format(pprint(e), pprint(ctx.e)))
        value = replace(e, arg, binder, match=alpha_equivalent)
        value = strip_EStateVar(value)
        # print(" ----> {}".format(pprint(value)))
        if any(v in args for v in free_vars(value)):
            continue
        for sv in state_vars:
            keys = reachable_values_of_type(sv, arg.type)
            # print("reachable values of type {}: {}".format(pprint(arg.type), pprint(keys)))
            # for v in state_vars:
            #     print("  {} : {}".format(pprint(v), pprint(v.type)))
            m = EMakeMap2(keys,
                ELambda(binder, value)).with_type(TMap(arg.type, e.type))
            assert not any(v in args for v in free_vars(m)), "oops! {}; args={}".format(pprint(m), ", ".join(pprint(a) for a in args))
            yield (m, STATE_POOL)
            mg = EMapGet(EStateVar(m).with_type(m.type), arg).with_type(e.type)
            # print(pprint(mg))
            # mg._tag = True
            yield (mg, RUNTIME_POOL)

def histogram(xs : Exp) -> Exp:
    elem_type = xs.type.t
    return EMakeMap2(xs,
        mk_lambda(elem_type, lambda x:
            ELen(EFilter(xs,
                mk_lambda(elem_type, lambda y:
                    EEq(x, y))).with_type(xs.type)))).with_type(TMap(elem_type, INT))

def optimized_count(x, xs):
    if isinstance(xs, EStateVar):
        m = histogram(xs.e)
        m = EStateVar(m).with_type(m.type)
        return EMapGet(m, x).with_type(INT)
    elif isinstance(xs, EBinOp) and xs.op == "-" and isinstance(xs.e2, ESingleton):
        return EBinOp(
            optimized_count(x, xs.e1), "-",
            optimized_cond(optimized_in(xs.e2.e, xs.e1), ONE, ZERO).with_type(INT)).with_type(INT)
    else:
        return ELen(EFilter(xs, mk_lambda(x.type, lambda y: EEq(x, y))).with_type(xs.type)).with_type(INT)

def optimized_any_matches(xs, p):
    if isinstance(xs, EEmptyList):
        return F
    elif isinstance(xs, ESingleton):
        return p.apply_to(xs.e)
    elif isinstance(xs, EMap):
        return optimized_any_matches(xs.e, compose(p, xs.f))
    elif isinstance(xs, EFilter):
        return optimized_any_matches(xs.e, ELambda(p.arg, EAll([p.body, xs.p.apply_to(p.arg)])))
    elif isinstance(xs, EBinOp) and xs.op == "+":
        return EAny([optimized_any_matches(xs.e1, p), optimized_any_matches(xs.e2, p)])
    elif isinstance(xs, ECond):
        return optimized_cond(xs.cond,
            optimized_any_matches(xs.then_branch, p),
            optimized_any_matches(xs.else_branch, p)).with_type(BOOL)
    else:
        return EUnaryOp(UOp.Exists, EFilter(xs, p).with_type(xs.type)).with_type(BOOL)

def optimized_in(x, xs):
    if isinstance(xs, EStateVar):
        m = EMakeMap2(xs.e, mk_lambda(x.type, lambda x: T)).with_type(TMap(x.type, BOOL))
        m = EStateVar(m).with_type(m.type)
        return EHasKey(m, x).with_type(BOOL)
    elif isinstance(xs, EBinOp) and xs.op == "-" and isinstance(xs.e1, EStateVar) and isinstance(xs.e2, ESingleton):
        return optimized_cond(optimized_eq(x, xs.e2.e),
            EGt(optimized_count(x, xs.e1), ONE),
            optimized_in(x, xs.e1)).with_type(BOOL)
    elif isinstance(xs, EBinOp) and xs.op == "-":
        return EGt(optimized_count(x, xs.e1), optimized_count(x, xs.e2))
    elif isinstance(xs, ECond):
        return optimized_cond(xs.cond,
            optimized_in(x, xs.then_branch),
            optimized_in(x, xs.else_branch)).with_type(BOOL)
    elif isinstance(xs, EFilter):
        return EAll([xs.p.apply_to(x), optimized_in(x, xs.e)])
    elif isinstance(xs, EMap) and xs.f.arg not in free_vars(x):
        return optimized_any_matches(xs.e, ELambda(xs.f.arg, optimized_eq(xs.f.body, x)))
    elif isinstance(xs, ESingleton):
        return optimized_eq(x, xs.e)
    elif isinstance(xs, EEmptyList):
        return F
    else:
        return EBinOp(x, BOp.In, xs).with_type(BOOL)

def optimized_len(xs):
    if isinstance(xs, EStateVar):
        return EStateVar(optimized_len(xs.e)).with_type(INT)
    elif isinstance(xs, EBinOp) and xs.op == "-" and isinstance(xs.e2, ESingleton):
        return EBinOp(
            optimized_len(xs.e1), "-",
            optimized_cond(optimized_in(xs.e2.e, xs.e1), ONE, ZERO).with_type(INT)).with_type(INT)
    elif isinstance(xs, ESingleton):
        return ONE
    elif isinstance(xs, EEmptyList):
        return ZERO
    elif isinstance(xs, EMap):
        return optimized_len(xs.e)
    else:
        return ELen(xs)

def optimized_empty(xs):
    l = optimized_len(xs)
    if isinstance(l, ENum):
        return T if l.val == 0 else F
    return optimized_eq(l, ZERO)

def optimized_exists(xs):
    l = optimized_len(xs)
    if isinstance(l, ENum):
        return F if l.val == 0 else T
    return EGt(l, ZERO)

def optimized_best(xs, keyfunc, op, args):
    argbest = EArgMin if op == "<" else EArgMax
    elem_type = xs.type.t
    if isinstance(xs, EBinOp) and xs.op == "-" and isinstance(xs.e1, EStateVar) and isinstance(xs.e2, ESingleton):
        heap_type, make_heap = (TMinHeap, EMakeMinHeap) if op == "<" else (TMaxHeap, EMakeMaxHeap)
        bag = xs.e1
        x = xs.e2.e
        h = make_heap(bag.e, keyfunc).with_type(heap_type(elem_type, keyfunc))
        prev_min = EStateVar(optimized_best(bag.e, keyfunc, op, args=args).with_type(elem_type)).with_type(elem_type)
        return optimized_cond(
            EAll([optimized_in(x, bag), optimized_eq(x, prev_min)]),
            EHeapPeek2(EStateVar(h).with_type(h.type), EStateVar(ELen(bag.e)).with_type(INT)).with_type(elem_type),
            prev_min)
    elif isinstance(xs, EEmptyList):
        return construct_value(elem_type)
    elif isinstance(xs, ESingleton):
        return xs.e
    elif isinstance(xs, EBinOp) and xs.op == "+":
        a_ex = optimized_exists(xs.e1)
        b_ex = optimized_exists(xs.e2)
        a_best = optimized_best(xs.e1, keyfunc, op, args=args)
        b_best = optimized_best(xs.e2, keyfunc, op, args=args)
        return optimized_cond(
            a_ex, optimized_cond(b_ex,
                optimized_cond(
                    EBinOp(keyfunc.apply_to(a_best), op, keyfunc.apply_to(b_best)).with_type(BOOL),
                    a_best,
                    b_best),
                a_best),
            b_best)
        # return argbest(EBinOp(
        #     ESingleton(optimized_best(xs.e1, keyfunc, op, args=args)).with_type(xs.type), "+",
        #     ESingleton(optimized_best(xs.e2, keyfunc, op, args=args)).with_type(xs.type)).with_type(xs.type), keyfunc).with_type(elem_type)
    elif isinstance(xs, EMap):
        return optimized_cond(
            optimized_exists(xs),
            xs.f.apply_to(optimized_best(xs.e, compose(keyfunc, xs.f), op, args)),
            construct_value(elem_type))
    elif isinstance(xs, EStateVar) and not any(v in args for v in free_vars(keyfunc)):
        return EStateVar(argbest(xs.e, keyfunc).with_type(elem_type)).with_type(elem_type)
    elif isinstance(xs, ECond):
        return optimized_cond(
            xs.cond,
            optimized_best(xs.then_branch, keyfunc, op, args=args),
            optimized_best(xs.else_branch, keyfunc, op, args=args))
    else:
        return argbest(xs, keyfunc).with_type(elem_type)

def optimized_cond(c, a, b):
    if c == T:
        return a
    elif c == F:
        return b
    else:
        return ECond(c, a, b).with_type(a.type)

def optimized_eq(a, b):
    if alpha_equivalent(a, b):
        return T
    else:
        return EEq(a, b)

def optimized_addr(e):
    while isinstance(e, EWithAlteredValue):
        e = e.handle
    return e

def optimized_val(e):
    if isinstance(e, EWithAlteredValue):
        return e.new_value
    return EGetField(e, "val").with_type(e.type.value_type)

def _simple_filter(xs, p, args):
    if p.body == T:
        return xs
    elif p.body == F:
        return EEmptyList().with_type(xs.type)
    elif isinstance(xs, EEmptyList):
        return xs
    elif isinstance(xs, EStateVar) and not any(v in args for v in free_vars(p)):
        return EStateVar(_simple_filter(xs.e, p, args)).with_type(xs.type)
    elif isinstance(p.body, EBinOp) and p.body.op == "==" and p.body.e1 == p.arg and p.arg not in free_vars(p.body.e2):
        return optimized_cond(
            optimized_in(p.body.e2, xs),
            ESingleton(p.body.e2).with_type(xs.type),
            EEmptyList().with_type(xs.type)).with_type(xs.type)
    else:
        return EFilter(xs, p).with_type(xs.type)

def optimized_bag_difference(xs, ys):
    # EStateVar(distinct xs) - (EStateVar(xs) - [i])
    # ===> is-last(i, xs) ? [] : [i]
    if (isinstance(ys, EBinOp) and ys.op == "-" and
            isinstance(ys.e1, EStateVar) and
            isinstance(ys.e2, ESingleton) and
            isinstance(xs, EStateVar) and isinstance(xs.e, EUnaryOp) and xs.e.op == UOp.Distinct and
            alpha_equivalent(xs.e.e, ys.e1.e)):
        distinct_elems = xs.e
        elems = distinct_elems.e
        elem_type = elems.type.t
        m = histogram(elems)
        m_rt = EStateVar(m).with_type(m.type)
        count = EMapGet(m_rt, ys.e2.e).with_type(INT)
        return optimized_cond(
            optimized_eq(count, ONE),
            ys.e2,
            EEmptyList().with_type(xs.type))

    # xs - (xs - [i])
    # ===> (i in xs) ? [i] : []
    if isinstance(ys, EBinOp) and ys.op == "-" and isinstance(ys.e2, ESingleton) and alpha_equivalent(xs, ys.e1):
        return optimized_cond(optimized_in(ys.e2.e, xs),
            ys.e2,
            EEmptyList().with_type(xs.type))

    # [x] - xs
    if isinstance(xs, ESingleton):
        return optimized_cond(
            optimized_in(xs.e, ys),
            EEmptyList().with_type(xs.type),
            xs)

    # only legal if xs are distinct, but we'll give it a go...
    return EFilter(xs, mk_lambda(xs.type.t, lambda x: ENot(optimized_in(x, ys)))).with_type(xs.type)

def optimize_filter_as_if_distinct(xs, p, args):
    if isinstance(xs, EBinOp) and xs.op == "-":
        return optimize_filter_as_if_distinct(xs.e1, ELambda(p.arg, EAll([ENot(optimized_in(p.arg, xs.e2)), p.body])), args)
    from cozy.syntax_tools import dnf, nnf
    cases = dnf(nnf(p.body))
    cases = [unique(c) for c in cases]
    # for c in cases:
    #     print("; ".join(pprint(x) for x in c))
    if len(cases) == 0:
        return EFilter(xs, p).with_type(xs.type)
    else:
        res = xs
        for c in sorted(unique(cases[0]), key=lambda c: 1 if any(v in args for v in free_vars(c)) else 0):
            res = _simple_filter(res, ELambda(p.arg, c), args)
        if cases[1:]:
            cond = EAll([ENot(EAll(cases[0])), EAny(EAll(c) for c in cases[1:])])
            res = EBinOp(res, "+", optimize_filter_as_if_distinct(xs, ELambda(p.arg, cond), args=args)).with_type(res.type)
        return res

def optimize_map(xs, f, args):
    res_type = TBag(f.body.type)
    if isinstance(xs, ESingleton):
        return ESingleton(f.apply_to(xs.e)).with_type(res_type)
    elif isinstance(xs, EEmptyList):
        return EEmptyList().with_type(res_type)
    elif isinstance(f.body, ECond):
        return EBinOp(
            optimize_map(optimize_filter_as_if_distinct(xs, ELambda(f.arg,      f.body.cond) , args=args), ELambda(f.arg, f.body.then_branch), args), "+",
            optimize_map(optimize_filter_as_if_distinct(xs, ELambda(f.arg, ENot(f.body.cond)), args=args), ELambda(f.arg, f.body.else_branch), args)).with_type(res_type)
    else:
        return EMap(xs, f).with_type(res_type)

def _check(e, pool):
    return e

def try_optimize(e, context, pool):
    if not accelerate.value:
        return
    # print("accelerating {} [in {}]".format(pprint(e), pool_name(pool)))

    state_vars = [v for v, p in context.vars() if p == STATE_POOL]
    args = [v for v, p in context.vars() if p == RUNTIME_POOL]

    ee = simplify(e)
    if not alpha_equivalent(ee, e):
        yield _check(simplify(e), pool)
    if pool == RUNTIME_POOL:
        if all(v in state_vars for v in free_vars(e)):
            nsv = strip_EStateVar(e)
            sv = EStateVar(nsv).with_type(e.type)
            yield _check(sv, RUNTIME_POOL)

        for e, p in map_accelerate(e, state_vars, args, None, 0):
            if p == RUNTIME_POOL:
                yield _check(e, p)

        if isinstance(e, EArgMin) or isinstance(e, EArgMax):
            ee = optimized_best(e.e, e.f, "<" if isinstance(e, EArgMin) else ">", args=args)
            if not alpha_equivalent(e, ee):
                yield _check(ee, RUNTIME_POOL)

        if is_collection(e.type) and isinstance(e, EBinOp) and e.op == "-":
            ee = optimized_bag_difference(e.e1, e.e2)
            if not alpha_equivalent(e, ee):
                yield _check(ee, RUNTIME_POOL)

        if isinstance(e, EBinOp) and e.op == "===" and isinstance(e.e1.type, THandle):
            yield _check(EAll([
                optimized_eq(optimized_addr(e.e1), optimized_addr(e.e2)),
                optimized_eq(optimized_val(e.e1),  optimized_val(e.e2)).with_type(BOOL)]), RUNTIME_POOL)

        if isinstance(e, EBinOp) and e.op == BOp.In:
            ee = optimized_in(e.e1, e.e2)
            if not alpha_equivalent(e, ee):
                yield _check(ee, RUNTIME_POOL)

        if isinstance(e, EUnaryOp) and e.op == UOp.Empty:
            ee = optimized_empty(e.e)
            if not alpha_equivalent(e, ee):
                yield _check(ee, RUNTIME_POOL)

        if isinstance(e, EUnaryOp) and e.op == UOp.Exists:
            ee = optimized_exists(e.e)
            if not alpha_equivalent(e, ee):
                yield _check(ee, RUNTIME_POOL)

        if isinstance(e, EUnaryOp) and e.op == UOp.Length:
            ee = optimized_len(e.e)
            if not alpha_equivalent(e, ee):
                yield _check(ee, RUNTIME_POOL)

        if isinstance(e, EFilter):
            ee = optimize_filter_as_if_distinct(e.e, e.p, args=args)
            if not alpha_equivalent(e, ee):
                yield _check(ee, RUNTIME_POOL)

        if isinstance(e, EMap):
            ee = optimize_map(e.e, e.f, args=args)
            if not alpha_equivalent(e, ee):
                yield _check(ee, RUNTIME_POOL)
