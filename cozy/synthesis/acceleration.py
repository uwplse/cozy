from cozy.common import unique
from cozy.target_syntax import *
from cozy.syntax_tools import fresh_var, free_vars, free_funcs, break_conj, mk_lambda, strip_EStateVar, alpha_equivalent, compose
from cozy.typecheck import is_collection, retypecheck
from cozy.contexts import shred, replace
from cozy.pools import RUNTIME_POOL, STATE_POOL
from cozy.structures.heaps import TMinHeap, TMaxHeap, EMakeMinHeap, EMakeMaxHeap, EHeapPeek2
from cozy.evaluation import construct_value, uneval, eval

accelerate = Option("acceleration-rules", bool, True)

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
    if isinstance(xs, ESingleton):
        return p.apply_to(xs.e)
    if isinstance(xs, EMap):
        return optimized_any_matches(xs.e, compose(p, xs.f))


    # exists filter (not-in xs) ys
    if isinstance(p.body, EUnaryOp) and p.body.op == UOp.Not and isinstance(p.body.e, EBinOp) and p.body.e.op == BOp.In:
        if p.arg not in free_vars(p.body.e.e2):
            # er, this only works when xs is a subset of ys
            return EGt(
                optimized_len(xs),
                optimized_len(p.body.e.e2))

    if isinstance(p.body, EBinOp) and p.body.op == BOp.Or:
        return EAny([
            optimized_any_matches(xs, ELambda(p.arg, p.body.e1)).with_type(xs.type),
            optimized_any_matches(xs, ELambda(p.arg, p.body.e2)).with_type(xs.type)])

    if isinstance(xs, EFilter):
        return optimized_any_matches(xs.e, ELambda(p.arg, EAll([p.body, xs.p.apply_to(p.arg)])))
    if isinstance(xs, EBinOp) and xs.op == "+":
        return EAny([optimized_any_matches(xs.e1, p), optimized_any_matches(xs.e2, p)])
    if isinstance(xs, EBinOp) and xs.op == "-":
        return EAll([
            optimized_any_matches(xs.e1, p),
            ENot(optimized_any_matches(xs.e2, p))])
    if isinstance(xs, ECond):
        return optimized_cond(xs.cond,
            optimized_any_matches(xs.then_branch, p),
            optimized_any_matches(xs.else_branch, p)).with_type(BOOL)

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
    elif isinstance(xs, EBinOp) and xs.op == "+":
        return EAny([
            optimized_in(x, xs.e1),
            optimized_in(x, xs.e2)])
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
    elif isinstance(xs, EBinOp) and xs.op == "+":
        return EBinOp(
            optimized_len(xs.e1), "+",
            optimized_len(xs.e2)).with_type(INT)
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
    if isinstance(xs, EFilter):
        return optimized_any_matches(xs.e, xs.p)
    elif isinstance(xs, EStateVar):
        return EStateVar(EUnaryOp(UOp.Exists, xs.e).with_type(BOOL)).with_type(BOOL)
    elif isinstance(xs, EBinOp) and xs.op == "+":
        return EAny([
            optimized_exists(xs.e1),
            optimized_exists(xs.e2)])
    elif isinstance(xs, EBinOp) and xs.op == "-":
        l = optimized_len(xs)
        if isinstance(l, ENum):
            return F if l.val == 0 else T
        return EGt(l, ZERO)
    elif isinstance(xs, ESingleton):
        return T
    elif isinstance(xs, EEmptyList):
        return F
    elif isinstance(xs, EMap):
        return optimized_exists(xs.e)
    elif isinstance(xs, EListSlice):
        return EAll([
            optimized_exists(xs.e),
            EGe(xs.start, ZERO),
            ELt(xs.start, optimized_len(xs.e)),
            ELt(xs.start, xs.end)])
    else:
        return EUnaryOp(UOp.Exists, xs).with_type(BOOL)

def is_lenof(e, xs):
    return alpha_equivalent(strip_EStateVar(e), ELen(strip_EStateVar(xs)))

def excluded_element(xs, args):
    if isinstance(xs, EMap):
        res = excluded_element(xs.e, args)
        if res is not None:
            bag, x = res
            return (EMap(bag, xs.f).with_type(xs.type), xs.f.apply_to(x))
    if isinstance(xs, EFilter):
        arg = xs.p.arg
        e = xs.p.body
        if isinstance(e, EUnaryOp) and e.op == UOp.Not and isinstance(e.e, EBinOp) and e.e.op == "==":
            e = EBinOp(e.e.e1, "!=", e.e.e2).with_type(BOOL)
        if isinstance(e, EBinOp) and e.op == "!=":
            arg_left = arg in free_vars(e.e1)
            arg_right = arg in free_vars(e.e2)
            if arg_left and not arg_right:
                return (xs.e, EUnaryOp(UOp.The, _simple_filter(xs.e, ELambda(arg, EEq(e.e1, e.e2)), args=args)).with_type(xs.type.t))
            if arg_right and not arg_left:
                return (xs.e, EUnaryOp(UOp.The, _simple_filter(xs.e, ELambda(arg, EEq(e.e1, e.e2)), args=args)).with_type(xs.type.t))
        return (xs.e, optimized_the(_simple_filter(xs.e, ELambda(xs.p.arg, ENot(xs.p.body)), args), args))
    if isinstance(xs, EBinOp) and xs.op == "-" and isinstance(xs.e2, ESingleton):
        return (xs.e1, xs.e2.e)
    if isinstance(xs, EBinOp) and xs.op == "-":
        return (xs.e1, optimized_the(xs.e2, args))
    if isinstance(xs, EBinOp) and xs.op == "+" and isinstance(xs.e1, EListSlice) and isinstance(xs.e2, EListSlice):
        for e1, e2 in [(xs.e1, xs.e2), (xs.e2, xs.e1)]:
            if e1.e == e2.e and e1.start == ZERO and e2.start == EBinOp(e1.end, "+", ONE) and is_lenof(e2.end, e2.e):
                return (e1.e, EListGet(e1.e, e1.end).with_type(xs.type.t))
    return None

def optimized_best(xs, keyfunc, op, args):
    argbest = EArgMin if op == "<" else EArgMax
    elem_type = xs.type.t
    key_type = keyfunc.body.type
    if excluded_element(xs, args) is not None:
        bag, x = excluded_element(xs, args)
        if all(v not in args for v in free_vars(bag)):
            heap_type, make_heap = (TMinHeap, EMakeMinHeap) if op == "<" else (TMaxHeap, EMakeMaxHeap)
            bag = EStateVar(strip_EStateVar(bag)).with_type(bag.type)
            h = make_heap(bag.e, keyfunc).with_type(heap_type(elem_type, key_type))
            for prev_min in optimized_best(bag.e, keyfunc, op, args=args):
                prev_min = EStateVar(prev_min).with_type(elem_type)
                heap_peek = EHeapPeek2(EStateVar(h).with_type(h.type), EStateVar(ELen(bag.e)).with_type(INT)).with_type(elem_type)
                conds = [optimized_in(x, bag), optimized_eq(x, prev_min)]
                if isinstance(x, EUnaryOp) and x.op == UOp.The:
                    conds = [optimized_exists(x.e)] + conds
                yield optimized_cond(
                    EAll(conds),
                    heap_peek,
                    prev_min)
    if isinstance(xs, EEmptyList):
        yield construct_value(elem_type)
    if isinstance(xs, ESingleton):
        yield xs.e
    if isinstance(xs, EBinOp) and xs.op == "+":
        a_ex = optimized_exists(xs.e1)
        b_ex = optimized_exists(xs.e2)
        bag_type = TBag(xs.type.t)
        for a in optimized_best(xs.e1, keyfunc, op, args=args):
            for b in optimized_best(xs.e2, keyfunc, op, args=args):
                yield optimized_cond(a_ex,
                    optimized_cond(b_ex,
                        argbest(EBinOp(ESingleton(a).with_type(bag_type), "+", ESingleton(b).with_type(bag_type)).with_type(bag_type), keyfunc).with_type(elem_type),
                        a),
                    optimized_cond(b_ex, b, construct_value(elem_type)))
        # if isinstance(xs.e1, EStateVar) or isinstance(xs.e2, EStateVar):
        #     sv, other = (xs.e1, xs.e2) if isinstance(xs.e1, EStateVar) else (xs.e2, xs.e1)
        #     sv_best = optimized_best(sv, keyfunc, op, args=args)
        #     yield optimized_cond(
        #         optimized_exists(sv),
        #         argbest(EBinOp(ESingleton(sv_best).with_type(xs.type), "+", other).with_type(xs.type), keyfunc).with_type(elem_type),
        #         optimized_best(other, keyfunc, op, args=args))
        # else:
        #     parts = break_sum(xs)
        #     found = F
        #     best = construct_value(elem_type)
        #     for p in parts:
        #         ex = optimized_exists(p)
        #         best_here = optimized_best(p, keyfunc, op, args=args)
        #         best = optimized_cond(found,
        #             optimized_cond(ex,
        #                 optimized_cond(EBinOp(keyfunc.apply_to(best_here), op, keyfunc.apply_to(best)).with_type(BOOL),
        #                     best_here,
        #                     best),
        #                 best),
        #             best_here)
        #         found = EAny([found, ex])
        #     yield best
    if isinstance(xs, EMap):
        for b in optimized_best(xs.e, compose(keyfunc, xs.f), op, args):
            yield optimized_cond(optimized_exists(xs.e),
                xs.f.apply_to(b),
                construct_value(elem_type))
    if isinstance(xs, EStateVar) and not any(v in args for v in free_vars(keyfunc)):
        yield EStateVar(argbest(xs.e, keyfunc).with_type(elem_type)).with_type(elem_type)
    if isinstance(xs, ECond):
        for a in optimized_best(xs.then_branch, keyfunc, op, args=args):
            for b in optimized_best(xs.else_branch, keyfunc, op, args=args):
                yield optimized_cond(xs.cond, a, b)
    if isinstance(xs, EUnaryOp) and xs.op == UOp.Distinct:
        yield from optimized_best(xs.e, keyfunc, op, args=args)
    # if isinstance(xs, EFilter):
    #     yield optimized_cond(
    #         xs.p.apply_to(optimized_best(xs.e, keyfunc, op, args=args)),
    #         optimized_best(xs.e, keyfunc, op, args=args),
    #         argbest(xs, keyfunc).with_type(elem_type))
    yield argbest(xs, keyfunc).with_type(elem_type)

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
    return e

def optimized_val(e):
    return EGetField(e, "val").with_type(e.type.value_type)

def mapkeys(m):
    if isinstance(m, EMakeMap2):
        return m.keys
    return EMapKeys(m).with_type(TBag(m.type.k))

def map_values(m, f):
    if isinstance(m, EMakeMap2):
        new_body = f(m.value.body)
        return EMakeMap2(m.e, ELambda(m.value.arg, new_body)).with_type(TMap(m.type.k, new_body.type))
    if isinstance(m, ECond):
        return optimized_cond(
            m.cond,
            map_values(m.then_branch, f),
            map_values(m.else_branch, f))

def _simple_filter(xs, p, args):
    if p.body == T:
        return xs
    if p.body == F:
        return EEmptyList().with_type(xs.type)
    if isinstance(xs, EEmptyList):
        return xs
    if isinstance(xs, EStateVar) and not any(v in args for v in free_vars(p)):
        return EStateVar(EFilter(xs.e, strip_EStateVar(p)).with_type(xs.type)).with_type(xs.type)
    if isinstance(xs, EMapGet) and isinstance(xs.map, EStateVar) and not any(v in args for v in free_vars(p)):
        m = map_values(xs.map.e, lambda ys: _simple_filter(ys, p, args))
        return EMapGet(EStateVar(m).with_type(m.type), xs.key).with_type(xs.type)
    if isinstance(xs, EBinOp) and xs.op == "+":
        return EBinOp(_simple_filter(xs.e1, p, args), "+", _simple_filter(xs.e2, p, args)).with_type(xs.type)
    if isinstance(p.body, EBinOp) and p.body.op == "==":
        fvs2 = free_vars(p.body.e2)
        fvs1 = free_vars(p.body.e1)
        if p.arg in fvs1 and not any(a in fvs1 for a in args) and p.arg not in fvs2 and isinstance(xs, EStateVar):
            k = fresh_var(p.body.e1.type)
            e = EMapGet(
                EStateVar(
                    EMakeMap2(
                        EMap(xs.e, ELambda(p.arg, p.body.e1)),
                        ELambda(k, EFilter(xs.e, ELambda(p.arg, EEq(p.body.e1, k)))))),
                p.body.e2)
            res = retypecheck(e)
            assert res
            return e
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

def optimize_filter_as_if_distinct(xs, p, args, dnf=True):
    if isinstance(xs, EBinOp) and xs.op == "-":
        return EBinOp(
            optimize_filter_as_if_distinct(xs.e1, p, args), "-",
            optimize_filter_as_if_distinct(xs.e2, p, args)).with_type(xs.type)
        # return optimize_filter_as_if_distinct(xs.e1, ELambda(p.arg, EAll([ENot(optimized_in(p.arg, xs.e2)), p.body])), args)

    if dnf:
        from cozy.syntax_tools import dnf, nnf
        cases = dnf(nnf(p.body))
        cases = [list(unique(c)) for c in cases]
        # for c in cases:
        #     print("; ".join(pprint(x) for x in c))
        assert cases
    else:
        cases = [list(break_conj(p.body))]

    res = xs
    for c in sorted(unique(cases[0]), key=lambda c: 1 if any(v in args for v in free_vars(c)) else 0):
        res = _simple_filter(res, ELambda(p.arg, c), args)
    if cases[1:]:
        cond = EAll([ENot(EAll(cases[0])), EAny(EAll(c) for c in cases[1:])])
        res = EBinOp(res, "+",
                optimize_filter_as_if_distinct(xs, ELambda(p.arg, cond), args=args, dnf=False)).with_type(res.type)
    return res

def optimize_map(xs, f, args):
    res_type = type(xs.type)(f.body.type)
    if isinstance(xs, ESingleton):
        yield ESingleton(f.apply_to(xs.e)).with_type(res_type)
    if isinstance(xs, EEmptyList):
        yield EEmptyList().with_type(res_type)
    if isinstance(xs, EBinOp):
        if xs.op == "+":
            for a in optimize_map(xs.e1, f, args):
                for b in optimize_map(xs.e2, f, args):
                    yield EBinOp(a, "+", b).with_type(res_type)
    if isinstance(f.body, ECond):
        for a     in optimize_map(optimize_filter_as_if_distinct(xs, ELambda(f.arg,      f.body.cond) , args=args), ELambda(f.arg, f.body.then_branch), args):
            for b in optimize_map(optimize_filter_as_if_distinct(xs, ELambda(f.arg, ENot(f.body.cond)), args=args), ELambda(f.arg, f.body.else_branch), args):
                yield EBinOp(a, "+", b).with_type(res_type)
    yield EMap(xs, f).with_type(res_type)

sum_of = lambda xs: EUnaryOp(UOp.Sum, xs).with_type(xs.type.t)

def optimized_sum(xs, args):
    elem_type = xs.type.t
    if isinstance(xs, EStateVar):
        yield EStateVar(sum_of(xs)).with_type(elem_type)
    if isinstance(xs, EBinOp) and xs.op == "+":
        for a in optimized_sum(xs.e1, args=args):
            for b in optimized_sum(xs.e2, args=args):
                yield EBinOp(a, "+", b).with_type(elem_type)
    if isinstance(xs, EBinOp) and xs.op == "-":
        arg = fresh_var(elem_type)
        for a in optimized_sum(xs.e1, args=args):
            for b in optimized_sum(_simple_filter(xs.e2, ELambda(arg, optimized_in(arg, xs.e1)), args).with_type(xs.type), args=args):
                yield EBinOp(a, "-", b).with_type(elem_type)
    x = excluded_element(xs, args)
    if x is not None:
        bag, x = x
        for s in optimized_sum(bag, args):
            yield EBinOp(s, "-", x).with_type(x.type)
    if isinstance(xs, ESingleton):
        yield xs.e
    yield sum_of(xs)

def optimized_the(xs, args):
    return EUnaryOp(UOp.The, xs).with_type(xs.type.t)

def optimize_the(xs, args):
    t = xs.type.t
    if isinstance(xs, ECond):
        for e1 in optimize_the(xs.then_branch, args):
            for e2 in optimize_the(xs.else_branch, args):
                yield optimized_cond(xs.cond, e1, e2)
    if isinstance(xs, EStateVar):
        yield EStateVar(EUnaryOp(UOp.The, xs.e).with_type(t)).with_type(t)
    if isinstance(xs.type, TList):
        x = excluded_element(xs, args)
        if x is not None:
            bag, x = x
            for elem in optimize_the(bag, args):
                yield optimized_cond(EEq(elem, x), EListGet(bag, ONE).with_type(t), elem)
    if isinstance(xs, EMap):
        exists = optimized_exists(xs.e)
        for x in optimize_the(xs.e, args):
            yield optimized_cond(exists, xs.f.apply_to(x), construct_value(t))
    if isinstance(xs, EBinOp) and xs.op == "+":
        e1_exists = optimized_exists(xs.e1)
        for x in optimize_the(xs.e1, args):
            for y in optimize_the(xs.e2, args):
                yield optimized_cond(e1_exists, x, y)
    yield EUnaryOp(UOp.The, xs).with_type(t)

def _check(e, context, pool):
    """
    When Cozy chokes on malformed expressions, bad acceleration rules are often
    the culprit.  To help debug these kinds of problems, this function exists
    as a "hook" where you can insert code to try and catch the issue before it
    leaks out.  Exceptions thrown here will reveal what acceleration rule is
    responsible for the problem.
    """
    return e

def fold_into_map(e, context):
    fvs = free_vars(e)
    state_vars = [v for v, p in context.vars() if p == STATE_POOL]
    for subexp, subcontext, subpool in shred(e, context, RUNTIME_POOL):
        if isinstance(subexp, EMapGet) and isinstance(subexp.map, EStateVar):
            map = subexp.map.e
            key = subexp.key
            key_type = key.type
            value_type = subexp.type
            # e is of the form `... EStateVar(map)[key] ...`
            arg = fresh_var(subexp.type, omit=fvs)
            func = ELambda(arg, replace(
                e, context, RUNTIME_POOL,
                subexp, subcontext, subpool,
                arg))
            if not all(v in state_vars for v in free_vars(func)):
                continue
            func = strip_EStateVar(func)
            key_arg = fresh_var(key_type, omit=fvs)
            new_map = EMakeMap2(
                EMapKeys(map).with_type(TSet(key_type)),
                ELambda(key_arg, func.apply_to(EMapGet(map, key_arg).with_type(value_type)))).with_type(TMap(key_type, e.type))
            yield EMapGet(EStateVar(new_map).with_type(new_map.type), key).with_type(e.type)

def _try_optimize(e, context, pool):
    if not accelerate.value:
        return

    state_vars = [v for v, p in context.vars() if p == STATE_POOL]
    args = [v for v, p in context.vars() if p == RUNTIME_POOL]

    if pool == RUNTIME_POOL:
        if not free_vars(e) and not free_funcs(e):
            yield _check(uneval(e.type, eval(e, {})), context, RUNTIME_POOL)

        if all(v in state_vars for v in free_vars(e)):
            nsv = strip_EStateVar(e)
            sv = EStateVar(nsv).with_type(e.type)
            yield _check(sv, context, RUNTIME_POOL)

        for ee in fold_into_map(e, context):
            yield _check(ee, context, pool)

        if isinstance(e, EListGet) and e.index == ZERO:
            yield _check(EUnaryOp(UOp.The, e.e).with_type(e.type), context, RUNTIME_POOL)

        if isinstance(e, EArgMin) or isinstance(e, EArgMax):
            for ee in optimized_best(e.e, e.f, "<" if isinstance(e, EArgMin) else ">", args=args):
                yield _check(ee, context, RUNTIME_POOL)

        if is_collection(e.type) and isinstance(e, EBinOp) and e.op == "-":
            ee = optimized_bag_difference(e.e1, e.e2)
            yield _check(ee, context, RUNTIME_POOL)

        if isinstance(e, EBinOp) and e.op == "===" and isinstance(e.e1.type, THandle):
            yield _check(EAll([
                optimized_eq(optimized_addr(e.e1), optimized_addr(e.e2)),
                optimized_eq(optimized_val(e.e1),  optimized_val(e.e2)).with_type(BOOL)]), context, RUNTIME_POOL)

        if isinstance(e, EBinOp) and e.op == BOp.In:
            ee = optimized_in(e.e1, e.e2)
            yield _check(ee, context, RUNTIME_POOL)

        if isinstance(e, EUnaryOp) and e.op == UOp.Sum:
            for ee in optimized_sum(e.e, args):
                yield _check(ee, context, RUNTIME_POOL)

        if isinstance(e, EUnaryOp) and e.op == UOp.Empty:
            ee = optimized_empty(e.e)
            yield _check(ee, context, RUNTIME_POOL)

        if isinstance(e, EUnaryOp) and e.op == UOp.Exists:
            ee = optimized_exists(e.e)
            yield _check(ee, context, RUNTIME_POOL)

        if isinstance(e, EUnaryOp) and e.op == UOp.Length:
            ee = optimized_len(e.e)
            yield _check(ee, context, RUNTIME_POOL)

        if isinstance(e, EUnaryOp) and e.op == UOp.The:
            for ee in optimize_the(e.e, args):
                yield _check(ee, context, RUNTIME_POOL)

        if isinstance(e, EFilter):
            ee = optimize_filter_as_if_distinct(e.e, e.p, args=args)
            yield _check(ee, context, RUNTIME_POOL)
            if isinstance(e.e, EFilter):
                # try swizzle
                ee = EFilter(_simple_filter(e.e.e, e.p, args=args), e.e.p).with_type(e.type)
                yield _check(ee, context, RUNTIME_POOL)

        if isinstance(e, EMap):
            for ee in optimize_map(e.e, e.f, args=args):
                yield _check(ee, context, RUNTIME_POOL)

def try_optimize(e, context, pool):
    for ee in _try_optimize(e, context, pool):
        if not alpha_equivalent(e, ee):
            yield ee
