import itertools
from functools import lru_cache

from cozy.common import find_one, partition, pick_to_sum, unique, OrderedSet
from cozy.target_syntax import *
from cozy.syntax_tools import fresh_var, free_vars, break_conj, pprint, enumerate_fragments, mk_lambda, strip_EStateVar, alpha_equivalent, subst, break_sum, replace, compose
from cozy.typecheck import is_numeric, is_collection, retypecheck
from cozy.pools import RUNTIME_POOL, STATE_POOL, ALL_POOLS, pool_name
from cozy.structures.heaps import TMinHeap, TMaxHeap, EMakeMinHeap, EMakeMaxHeap, EHeapPeek, EHeapPeek2
from cozy.evaluation import construct_value
from cozy.logging import task, event
from cozy.cost_model import is_constant_time

accelerate = Option("acceleration-rules", bool, True)

def EUnion(es):
    es = [e for x in es for e in break_sum(x) if e != EEmptyList()]
    if not es:
        return EEmptyList()
    return build_balanced_tree(es[0].type, "+", es)

def MkFlatMap(bag, f):
    if isinstance(f.body, ESingleton):
        if f.body.e == f.arg:
            return bag
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

def map_accelerate(e, context):
    with task("map_accelerate", size=e.size()):
        if is_constant_time(e):
            event("skipping map lookup inference for constant-time exp: {}".format(pprint(e)))
            return

        @lru_cache()
        def make_binder(t):
            return fresh_var(t, hint="key")

        args = OrderedSet(v for (v, p) in context.vars() if p == RUNTIME_POOL)
        possible_keys = { } # type -> [exp]
        i = 0

        stk = [e]
        while stk:
            event("exp {} / {}".format(i, e.size()))
            i += 1
            arg = stk.pop()
            if isinstance(arg, tuple):
                stk.extend(arg)
                continue
            if not isinstance(arg, Exp):
                continue
            if isinstance(arg, ELambda):
                stk.append(arg.body)
                continue

            if context.legal_for(free_vars(arg)):
                # all the work happens here
                binder = make_binder(arg.type)
                value = replace(e, arg, binder, match=lambda e1, e2: type(e1) == type(e2) and e1.type == e2.type and alpha_equivalent(e1, e2))
                value = strip_EStateVar(value)
                # print(" ----> {}".format(pprint(value)))
                if any(v in args for v in free_vars(value)):
                    event("not all args were eliminated")
                else:
                    if arg.type not in possible_keys:
                        l = [reachable_values_of_type(sv, arg.type)
                            for (sv, p) in context.vars() if p == STATE_POOL]
                        l = OrderedSet(x for x in l if not isinstance(x, EEmptyList))
                        possible_keys[arg.type] = l
                    for keys in possible_keys[arg.type]:
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

            if isinstance(arg, EStateVar):
                # do not visit state expressions
                continue

            num_with_args = 0
            stk2 = list(arg.children())
            while stk2:
                child = stk2.pop()
                if isinstance(child, tuple):
                    stk.extend(child)
                    continue
                if not isinstance(child, Exp):
                    continue
                fvs = free_vars(child)
                if fvs & args:
                    num_with_args += 1
                    if num_with_args >= 2:
                        break
            if num_with_args < 2:
                stk.extend(arg.children())
            else:
                event("refusing to visit children of {}".format(pprint(arg)))

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
    if isinstance(xs, EFilter) and isinstance(xs.p.body, EBinOp) and xs.p.body.op == BOp.Or:
        return EAny([
            optimized_exists(EFilter(xs.e, ELambda(xs.p.arg, xs.p.body.e1)).with_type(xs.type)),
            optimized_exists(EFilter(xs.e, ELambda(xs.p.arg, xs.p.body.e2)).with_type(xs.type))])
    elif isinstance(xs, EStateVar):
        return EStateVar(optimized_exists(xs.e)).with_type(BOOL)
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
    else:
        return EUnaryOp(UOp.Exists, xs).with_type(BOOL)

def excluded_element(xs, args):
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
    if isinstance(xs, EBinOp) and xs.op == "-" and isinstance(xs.e2, ESingleton):
        return (xs.e1, xs.e2.e)
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
            prev_min = EStateVar(optimized_best(bag.e, keyfunc, op, args=args).with_type(elem_type)).with_type(elem_type)
            heap_peek = EHeapPeek2(EStateVar(h).with_type(h.type), EStateVar(ELen(bag.e)).with_type(INT)).with_type(elem_type)
            return optimized_cond(
                EAll([optimized_in(x, bag), optimized_eq(x, prev_min)]),
                heap_peek,
                prev_min)
    if isinstance(xs, EEmptyList):
        return construct_value(elem_type)
    if isinstance(xs, ESingleton):
        return xs.e
    if isinstance(xs, EBinOp) and xs.op == "+":
        if isinstance(xs.e1, EStateVar) or isinstance(xs.e2, EStateVar):
            sv, other = (xs.e1, xs.e2) if isinstance(xs.e1, EStateVar) else (xs.e2, xs.e1)
            sv_best = optimized_best(sv, keyfunc, op, args=args)
            return optimized_cond(
                optimized_exists(sv),
                argbest(EBinOp(ESingleton(sv_best).with_type(xs.type), "+", other).with_type(xs.type), keyfunc).with_type(elem_type),
                optimized_best(other, keyfunc, op, args=args))
        else:
            parts = break_sum(xs)
            found = F
            best = construct_value(elem_type)
            for p in parts:
                ex = optimized_exists(p)
                best_here = optimized_best(p, keyfunc, op, args=args)
                best = optimized_cond(found,
                    optimized_cond(ex,
                        optimized_cond(EBinOp(keyfunc.apply_to(best_here), op, keyfunc.apply_to(best)).with_type(BOOL),
                            best_here,
                            best),
                        best),
                    best_here)
                found = EAny([found, ex])
            return best
    if isinstance(xs, EMap):
        return xs.f.apply_to(optimized_best(xs.e, compose(keyfunc, xs.f), op, args))
    if isinstance(xs, EStateVar) and not any(v in args for v in free_vars(keyfunc)):
        return EStateVar(argbest(xs.e, keyfunc).with_type(elem_type)).with_type(elem_type)
    if isinstance(xs, ECond):
        return optimized_cond(
            xs.cond,
            optimized_best(xs.then_branch, keyfunc, op, args=args),
            optimized_best(xs.else_branch, keyfunc, op, args=args))
    if isinstance(xs, EUnaryOp) and xs.op == UOp.Distinct:
        return optimized_best(xs.e, keyfunc, op, args=args)
    # if isinstance(xs, EFilter):
    #     return optimized_cond(
    #         xs.p.apply_to(optimized_best(xs.e, keyfunc, op, args=args)),
    #         optimized_best(xs.e, keyfunc, op, args=args),
    #         argbest(xs, keyfunc).with_type(elem_type))
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
    if isinstance(p.body, EBinOp) and p.body.op == "==":
        fvs2 = free_vars(p.body.e2)
        if p.body.e1 == p.arg and p.arg not in fvs2:
            return optimized_cond(
                optimized_in(p.body.e2, xs),
                ESingleton(p.body.e2).with_type(xs.type),
                EEmptyList().with_type(xs.type)).with_type(xs.type)
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
    if isinstance(xs, ESingleton):
        yield xs.e
    yield sum_of(xs)

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

def _try_optimize(e, context, pool):
    if not accelerate.value:
        return

    state_vars = [v for v, p in context.vars() if p == STATE_POOL]
    args = [v for v, p in context.vars() if p == RUNTIME_POOL]

    if pool == RUNTIME_POOL:
        if all(v in state_vars for v in free_vars(e)):
            nsv = strip_EStateVar(e)
            sv = EStateVar(nsv).with_type(e.type)
            yield _check(sv, context, RUNTIME_POOL)

        for ee, p in map_accelerate(e, context):
            if p == RUNTIME_POOL:
                yield _check(ee, context, p)

        if isinstance(e, EArgMin) or isinstance(e, EArgMax):
            ee = optimized_best(e.e, e.f, "<" if isinstance(e, EArgMin) else ">", args=args)
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
