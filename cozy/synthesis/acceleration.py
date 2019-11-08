"""Rewrite rules to optimize expressions.

Cozy's synthesis procedure uses `try_optimize` to try to produce better
versions of expressions it sees.  Since all expressions are checked for
correctness, `try_optimize` has a very loose contract.
"""

import itertools

from cozy.common import find_one
from cozy.target_syntax import *
from cozy.syntax_tools import fresh_var, free_vars, free_funcs, mk_lambda, strip_EStateVar, alpha_equivalent, compose, nnf, map_value_func
from cozy.typecheck import is_collection, retypecheck
from cozy.contexts import Context, all_subexpressions_with_context_information, replace
from cozy.pools import Pool, RUNTIME_POOL, STATE_POOL
from cozy.structures.heaps import TMinHeap, TMaxHeap, EMakeMinHeap, EMakeMaxHeap, EHeapPeek2
from cozy.evaluation import construct_value, uneval, eval
from cozy.opts import Option
from cozy.wf import repair_well_formedness

accelerate = Option("acceleration-rules", bool, True,
    description="Enable rewrite rules that try to optimize "
        + "expressions during synthesis. This usually "
        + "improves Cozy's performance.")

def find_one_or_fail(iter):
    res = find_one(iter)
    if res is None:
        raise ValueError()
    return res

def try_optimize(e : Exp, context : Context, pool : Pool):
    """Yields expressions for the given context and pool.

    The expressions are likely to be semantically equivalent to `e` and likely
    to be better than `e`, but this function makes no promises.

    None of the expressions will be syntactically equivalent to `e`.
    """
    for ee in _try_optimize(e, context, pool):
        if not alpha_equivalent(e, ee):
            yield ee

def _try_optimize(e : Exp, context : Context, pool : Pool):
    if not accelerate.value:
        return

    if pool != RUNTIME_POOL:
        return

    state_vars = [v for v, p in context.vars() if p == STATE_POOL]
    args = [v for v, p in context.vars() if p == RUNTIME_POOL]

    # ---------------------------------------------------------------------
    # "Rewrite schemes": these trigger on many different AST shapes
    # They are listed first because they are more powerful than the
    # specific rewrite rules below.

    if not free_vars(e) and not free_funcs(e):
        try:
            yield _check(uneval(e.type, eval(e, {})), context, RUNTIME_POOL)
        except NotImplementedError:
            print("Unable to evaluate {!r}".format(e))

    if all(v in state_vars for v in free_vars(e)):
        nsv = strip_EStateVar(e)
        sv = EStateVar(nsv).with_type(e.type)
        yield _check(sv, context, RUNTIME_POOL)

    for ee in fold_into_map(e, context):
        yield _check(ee, context, pool)

    # ---------------------------------------------------------------------
    # "Rewrites": these trigger on specific AST nodes

    if isinstance(e, EBinOp):

        if e.op == "-" and is_collection(e.type):
            ee = optimized_bag_difference(e.e1, e.e2)
            yield _check(ee, context, RUNTIME_POOL)

        if e.op == "===" and isinstance(e.e1.type, THandle):
            yield _check(EAll([
                optimized_eq(optimized_addr(e.e1), optimized_addr(e.e2)),
                optimized_eq(optimized_val(e.e1),  optimized_val(e.e2)).with_type(BOOL)]), context, RUNTIME_POOL)

        if e.op == BOp.In:
            ee = optimized_in(e.e1, e.e2)
            yield _check(ee, context, RUNTIME_POOL)

    if isinstance(e, ECond):
        yield _check(optimized_cond(e.cond, e.then_branch, e.else_branch), context, RUNTIME_POOL)

    if isinstance(e, EGetField):
        for ee in optimized_get_field(e.e, e.field_name, args):
            yield _check(ee, context, RUNTIME_POOL)

    if isinstance(e, EListGet) and e.index == ZERO:
        for res in optimized_the(e.e, args):
            yield _check(res, context, RUNTIME_POOL)

    if isinstance(e, EListGet) and isinstance(e.e, ECond):
        yield optimized_cond(e.e.cond,
                             EListGet(e.e.then_branch, e.index).with_type(e.type),
                             EListGet(e.e.else_branch, e.index).with_type(e.type))

    from cozy.structures.treemultiset import ETreeMultisetElems, ETreeMultisetPeek
    if isinstance(e, EListGet) and isinstance(e.e, ETreeMultisetElems):
        yield ETreeMultisetPeek(e.e.e, e.index).with_type(e.type)

    if isinstance(e, EMapGet):
        ee = inline_mapget(e, context)
        yield _check(ee, context, RUNTIME_POOL)

    if isinstance(e, EUnaryOp):

        if e.op == UOp.Sum:
            for ee in optimized_sum(e.e, args):
                yield _check(ee, context, RUNTIME_POOL)

        if e.op == UOp.Length:
            ee = optimized_len(e.e)
            yield _check(ee, context, RUNTIME_POOL)

        if e.op == UOp.Empty:
            ee = optimized_empty(e.e)
            yield _check(ee, context, RUNTIME_POOL)

        if e.op == UOp.Exists:
            ee = optimized_exists(e.e)
            yield _check(ee, context, RUNTIME_POOL)

        if e.op == UOp.Distinct:
            for ee in optimized_distinct(e.e, args):
                yield _check(ee, context, RUNTIME_POOL)

        if e.op == UOp.The:
            for ee in optimized_the(e.e, args):
                yield _check(ee, context, RUNTIME_POOL)

    if isinstance(e, EArgMin) or isinstance(e, EArgMax):
        for ee in optimized_best(e.e, e.key_function, "<" if isinstance(e, EArgMin) else ">", args=args):
            yield _check(ee, context, RUNTIME_POOL)

    if isinstance(e, EFilter):
        for ee in optimized_filter(e.e, e.predicate, args=args):
            yield _check(ee, context, RUNTIME_POOL)

    if isinstance(e, EMap):
        for ee in optimized_map(e.e, e.transform_function, args=args):
            yield _check(ee, context, RUNTIME_POOL)
    if isinstance(e, EFlatMap):
        for ee in optimized_flatmap(e.e, e.transform_function, args=args):
            yield _check(ee, context, RUNTIME_POOL)
    from cozy.syntax import ESorted
    from cozy.structures.treemultiset import EMakeMaxTreeMultiset, TMaxTreeMultiset, EMakeMinTreeMultiset, TMinTreeMultiset, ETreeMultisetElems
    target = e
    if isinstance(target, ESorted) and isinstance(target.e, EEmptyList):
        yield _check(target.e, context, RUNTIME_POOL)
    if isinstance(target, ESorted) and isinstance(target.e, EStateVar):
        e_max = EMakeMaxTreeMultiset(target.e.e).with_type(TMaxTreeMultiset(target.e.e.type.elem_type))
        e_min = EMakeMinTreeMultiset(target.e.e).with_type(TMinTreeMultiset(target.e.e.type.elem_type))
        ee = optimized_cond(target.asc,
                            ETreeMultisetElems(EStateVar(e_min).with_type(e_min.type)).with_type(target.type),
                            ETreeMultisetElems(EStateVar(e_max).with_type(e_max.type)).with_type(target.type))
        yield _check(ee, context, RUNTIME_POOL)

def _check(e : Exp, context : Context, pool : Pool):
    """
    When Cozy chokes on malformed expressions, bad acceleration rules are often
    the culprit.  To help debug these kinds of problems, this function exists
    as a "hook" where you can insert code to catch the issue before it
    leaks out.  Exceptions thrown here will reveal what acceleration rule is
    responsible for the problem.
    """
    return e

def histogram(xs : Exp) -> Exp:
    """Compute a histogram of the given collection.

    This function takes a collection-type expression `xs` and returns a
    map-type expression.  The new expression constructs a map from elements of
    `xs` to the number of times they occur in `xs` (i.e. a histogram of the
    elements).
    """
    elem_type = xs.type.elem_type
    return EMakeMap2(xs,
        mk_lambda(elem_type, lambda x:
            ELen(EFilter(xs,
                mk_lambda(elem_type, lambda y:
                    EEq(x, y))).with_type(xs.type)))).with_type(TMap(elem_type, INT))

def inline_mapget(e : EMapGet, context : Context) -> Exp:
    try:
        keys = mapkeys(e.map)
        cond = optimized_in(e.key, keys)
        f = map_value_func(e.map)
        return optimized_cond(
            cond,
            repair_well_formedness(f.apply_to(e.key), context),
            construct_value(e.type))
    except:
        pass
    print("warning: unable to inline {}".format(e))
    return e

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
        return EFALSE
    if isinstance(xs, ESingleton):
        return p.apply_to(xs.e)
    if isinstance(xs, EMap):
        return optimized_any_matches(xs.e, compose(p, xs.transform_function))


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
        return optimized_any_matches(xs.e, ELambda(p.arg, EAll([p.body, xs.predicate.apply_to(p.arg)])))
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
        m = EMakeMap2(xs.e, mk_lambda(x.type, lambda x: ETRUE)).with_type(TMap(x.type, BOOL))
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
        return EAll([xs.predicate.apply_to(x), optimized_in(x, xs.e)])
    elif isinstance(xs, EMap) and xs.transform_function.arg not in free_vars(x):
        return optimized_any_matches(xs.e, ELambda(xs.transform_function.arg, optimized_eq(xs.transform_function.body, x)))
    elif isinstance(xs, ESingleton):
        return optimized_eq(x, xs.e)
    elif isinstance(xs, EEmptyList):
        return EFALSE
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
        return ETRUE if l.val == 0 else EFALSE
    return optimized_eq(l, ZERO)

def optimized_exists(xs):
    if isinstance(xs, EFilter):
        return optimized_any_matches(xs.e, xs.predicate)
    elif isinstance(xs, EStateVar):
        return statevar(EUnaryOp(UOp.Exists, xs.e), BOOL)
    elif isinstance(xs, EBinOp) and xs.op == "+":
        return EAny([
            optimized_exists(xs.e1),
            optimized_exists(xs.e2)])
    elif isinstance(xs, EBinOp) and xs.op == "-":
        l = optimized_len(xs)
        if isinstance(l, ENum):
            return EFALSE if l.val == 0 else ETRUE
        return EGt(l, ZERO)
    elif isinstance(xs, ESingleton):
        return ETRUE
    elif isinstance(xs, EEmptyList):
        return EFALSE
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
            return (EMap(bag, xs.transform_function).with_type(xs.type), xs.transform_function.apply_to(x))
    if isinstance(xs, EFilter):
        arg = xs.predicate.arg
        e = xs.predicate.body
        if isinstance(e, EUnaryOp) and e.op == UOp.Not and isinstance(e.e, EBinOp) and e.e.op == "==":
            e = EBinOp(e.e.e1, "!=", e.e.e2).with_type(BOOL)
        if isinstance(e, EBinOp) and e.op == "!=":
            arg_left = arg in free_vars(e.e1)
            arg_right = arg in free_vars(e.e2)
            if arg_left and not arg_right:
                return (xs.e, EUnaryOp(UOp.The, find_one_or_fail(_simple_filter(xs.e, ELambda(arg, EEq(e.e1, e.e2)), args=args))).with_type(xs.type.elem_type))
            if arg_right and not arg_left:
                return (xs.e, EUnaryOp(UOp.The, find_one_or_fail(_simple_filter(xs.e, ELambda(arg, EEq(e.e1, e.e2)), args=args))).with_type(xs.type.elem_type))
        return (xs.e, EFirst(find_one_or_fail(_simple_filter(xs.e, ELambda(xs.predicate.arg, ENot(xs.predicate.body)), args))))
    if isinstance(xs, EBinOp) and xs.op == "-" and isinstance(xs.e2, ESingleton):
        return (xs.e1, xs.e2.e)
    if isinstance(xs, EBinOp) and xs.op == "-":
        return (xs.e1, EFirst(xs.e2))
    if isinstance(xs, EBinOp) and xs.op == "+" and isinstance(xs.e1, EListSlice) and isinstance(xs.e2, EListSlice):
        for e1, e2 in [(xs.e1, xs.e2), (xs.e2, xs.e1)]:
            if e1.e == e2.e and e1.start == ZERO and e2.start == EBinOp(e1.end, "+", ONE) and is_lenof(e2.end, e2.e):
                return (e1.e, EListGet(e1.e, e1.end).with_type(xs.type.elem_type))
    return None

from cozy.syntax_tools import pprint

def optimized_best(xs, keyfunc, op, args):
    argbest = EArgMin if op == "<" else EArgMax
    elem_type = xs.type.elem_type
    key_type = keyfunc.body.type
    if excluded_element(xs, args) is not None:
        bag, x = excluded_element(xs, args)
        if all(v not in args for v in free_vars(bag)):
            heap_type, make_heap = (TMinHeap, EMakeMinHeap) if op == "<" else (TMaxHeap, EMakeMaxHeap)
            bag = EStateVar(strip_EStateVar(bag)).with_type(bag.type)
            h = make_heap(bag.e, keyfunc).with_type(heap_type(elem_type, key_type))
            for prev_min in optimized_best(bag.e, keyfunc, op, args=args):
                prev_min = EStateVar(prev_min).with_type(elem_type)
                heap_peek = EHeapPeek2(EStateVar(h).with_type(h.type)).with_type(elem_type)
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
        bag_type = TBag(xs.type.elem_type)
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
        #     found = EFALSE
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
        for b in optimized_best(xs.e, compose(keyfunc, xs.transform_function), op, args):
            yield optimized_cond(optimized_exists(xs.e),
                xs.transform_function.apply_to(b),
                construct_value(elem_type))
    if isinstance(xs, EStateVar) and not any(v in args for v in free_vars(keyfunc)):
        yield statevar(argbest(xs.e, keyfunc), elem_type)
    if isinstance(xs, ECond):
        for a in optimized_best(xs.then_branch, keyfunc, op, args=args):
            for b in optimized_best(xs.else_branch, keyfunc, op, args=args):
                yield optimized_cond(xs.cond, a, b)
    if isinstance(xs, EUnaryOp) and xs.op == UOp.Distinct:
        yield from optimized_best(xs.e, keyfunc, op, args=args)
    # if isinstance(xs, EFilter):
    #     yield optimized_cond(
    #         xs.predicate.apply_to(optimized_best(xs.e, keyfunc, op, args=args)),
    #         optimized_best(xs.e, keyfunc, op, args=args),
    #         argbest(xs, keyfunc).with_type(elem_type))
    yield argbest(xs, keyfunc).with_type(elem_type)

def optimized_cond(c, a, b):
    if c == ETRUE:
        return a
    elif c == EFALSE:
        return b
    else:
        return ECond(c, a, b).with_type(a.type)

def optimized_eq(a, b):
    if alpha_equivalent(a, b):
        return ETRUE
    else:
        return EEq(a, b)

def optimized_addr(e):
    return e

def optimized_val(e):
    return EGetField(e, "val").with_type(e.type.value_type)

def optimized_get_field(e, f, args):
    if isinstance(e.type, THandle) and f == "val":
        yield optimized_val(e)
    elif isinstance(e, EStateVar):
        for gf in optimized_get_field(e.e, f, args):
            yield EStateVar(gf).with_type(gf.type)
    elif isinstance(e, EMakeRecord):
        yield dict(e.fields)[f]
    elif isinstance(e, ECond):
        for then_case in optimized_get_field(e.then_branch, f, args):
            for else_case in optimized_get_field(e.else_branch, f, args):
                yield optimized_cond(e.cond, then_case, else_case)
    elif isinstance(e.type, TRecord):
        yield EGetField(e, f).with_type(dict(e.type.fields)[f])
    else:
        pass

def mapkeys(m):
    if isinstance(m, EMakeMap2):
        return m.e
    if isinstance(m, EStateVar):
        keys = mapkeys(m.e)
        return EStateVar(keys).with_type(keys.type)
    return EMapKeys(m).with_type(TBag(m.type.k))

def map_values_multi(m, f):
    if isinstance(m, EMakeMap2):
        for new_body in f(m.value_function.body):
            yield EMakeMap2(m.e, ELambda(m.value_function.arg, new_body)).with_type(TMap(m.type.k, new_body.type))
    if isinstance(m, ECond):
        for then_branch in map_values_multi(m.then_branch, f):
            for else_branch in map_values_multi(m.else_branch, f):
                yield optimized_cond(m.cond, then_branch, else_branch)

def map_values(m, f):
    return find_one_or_fail(map_values_multi(m, lambda body: [f(body)]))

def _simple_filter(xs : Exp, p : ELambda, args : {EVar}):
    """Assumes the body of p is already in negation normal form"""
    if p.body == ETRUE:
        yield xs
        return
    if p.body == EFALSE:
        yield EEmptyList().with_type(xs.type)
        return
    if isinstance(xs, EEmptyList):
        yield xs
        return
    yielded = False
    if isinstance(xs, ESingleton):
        yielded = True
        yield optimized_cond(p.apply_to(xs.e), xs, EEmptyList().with_type(xs.type))
    if isinstance(p.body, EBinOp) and p.body.op == BOp.Or:
        for e1, e2 in itertools.permutations([p.body.e1, p.body.e2]):
            for r1 in _simple_filter(xs, ELambda(p.arg, e1), args):
                for r2 in _simple_filter(xs, ELambda(p.arg, EAll([e2, ENot(e1)])), args):
                    yielded = True
                    yield EBinOp(r1, "+", r2).with_type(xs.type)
    if isinstance(p.body, EBinOp) and p.body.op == BOp.And:
        for e1, e2 in itertools.permutations([p.body.e1, p.body.e2]):
            for r1 in _simple_filter(xs, ELambda(p.arg, e1), args):
                yielded = True
                yield from _simple_filter(r1, ELambda(p.arg, e2), args)
    if isinstance(xs, EStateVar) and not any(v in args for v in free_vars(p)):
        yielded = True
        yield EStateVar(EFilter(xs.e, strip_EStateVar(p)).with_type(xs.type)).with_type(xs.type)
    if isinstance(xs, EMapGet) and isinstance(xs.map, EStateVar) and not any(v in args for v in free_vars(p)):
        for m in map_values_multi(xs.map.e, lambda ys: _simple_filter(ys, p, args)):
            yielded = True
            yield EMapGet(EStateVar(m).with_type(m.type), xs.key).with_type(xs.type)
    if isinstance(xs, EBinOp) and xs.op in ("+", "-"):
        for e1 in _simple_filter(xs.e1, p, args):
            for e2 in _simple_filter(xs.e2, p, args):
                yielded = True
                yield EBinOp(e1, xs.op, e2).with_type(xs.type)
    if isinstance(p.body, EBinOp) and p.body.op == "==":
        e1 = p.body.e1
        e2 = p.body.e2
        fvs2 = free_vars(e2)
        fvs1 = free_vars(e1)
        for (e1, fvs1), (e2, fvs2) in itertools.permutations([(e1, fvs1), (e2, fvs2)]):
            if p.arg in fvs1 and not any(a in fvs1 for a in args) and p.arg not in fvs2 and isinstance(xs, EStateVar):
                if e1 == p.arg:
                    yield optimized_cond(
                        optimized_in(e2, xs),
                        ESingleton(e2).with_type(xs.type),
                        EEmptyList().with_type(xs.type))

                k = fresh_var(e1.type)
                e = EMapGet(
                    EStateVar(
                        EMakeMap2(
                            EMap(xs.e, ELambda(p.arg, e1)),
                            ELambda(k, EFilter(xs.e, ELambda(p.arg, EEq(e1, k)))))),
                    e2)
                res = retypecheck(e)
                assert res
                yielded = True
                yield e
    if not yielded:
        yield EFilter(xs, p).with_type(xs.type)

def optimized_filter(xs : Exp, p : ELambda, args : {EVar}):
    yield from _simple_filter(xs, ELambda(p.arg, nnf(p.body)), args)

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
        elem_type = elems.type.elem_type
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
    return EFilter(xs, mk_lambda(xs.type.elem_type, lambda x: ENot(optimized_in(x, ys)))).with_type(xs.type)

def optimized_map(xs, f, args):
    res_type = type(xs.type)(f.body.type)
    if f.arg == f.body:
        yield xs
    if isinstance(xs, ESingleton):
        yield ESingleton(f.apply_to(xs.e)).with_type(res_type)
    if isinstance(xs, EEmptyList):
        yield EEmptyList().with_type(res_type)
    if isinstance(xs, EStateVar) and not any(v in args for v in free_vars(f)):
        yield EStateVar(EMap(xs.e, f).with_type(res_type)).with_type(res_type)
    if isinstance(xs, EBinOp):
        if xs.op in ("+", "-"):
            for a in optimized_map(xs.e1, f, args):
                for b in optimized_map(xs.e2, f, args):
                    yield EBinOp(a, xs.op, b).with_type(res_type)
    if isinstance(f.body, ECond):
        for true_elems      in optimized_filter(xs, ELambda(f.arg,      f.body.cond) , args=args):
            for false_elems in optimized_filter(xs, ELambda(f.arg, ENot(f.body.cond)), args=args):
                for a     in optimized_map(true_elems,  ELambda(f.arg, f.body.then_branch), args):
                    for b in optimized_map(false_elems, ELambda(f.arg, f.body.else_branch), args):
                        yield EBinOp(a, "+", b).with_type(res_type)
    yield EMap(xs, f).with_type(res_type)

sum_of = lambda xs: EUnaryOp(UOp.Sum, xs).with_type(xs.type.elem_type)

def optimized_sum(xs, args, inplace_opt=True):
    """
    :param xs:
    :param args:
    :param inplace_opt: whether to apply inplace optimization, which might cause infinite recursive
    :return:
    """
    elem_type = xs.type.elem_type
    if isinstance(xs, EStateVar):
        yield EStateVar(sum_of(strip_EStateVar(xs))).with_type(elem_type)
    if isinstance(xs, EBinOp) and xs.op == "+":
        for a in optimized_sum(xs.e1, args=args):
            for b in optimized_sum(xs.e2, args=args):
                yield EBinOp(a, "+", b).with_type(elem_type)
    if isinstance(xs, EBinOp) and xs.op == "-":
        arg = fresh_var(elem_type)
        for a in optimized_sum(xs.e1, args=args):
            for e2 in _simple_filter(xs.e2, ELambda(arg, optimized_in(arg, xs.e1)), args):
                for b in optimized_sum(e2, args=args):
                    yield EBinOp(a, "-", b).with_type(elem_type)
    x = excluded_element(xs, args)
    if x is not None:
        bag, x = x
        for s in optimized_sum(bag, args):
            yield EBinOp(s, "-", x).with_type(x.type)
    if isinstance(xs, ESingleton):
        yield xs.e
    if isinstance(xs, EFlatMap):
        f = xs.transform_function
        # sum flatMap(e1 + e2, f) == sum flatMap(e1, f) + sum flatMap(e2, f)
        if isinstance(f.body, EBinOp) and f.body.op == "+":
            for e1 in optimized_flatmap(xs.e, ELambda(f.arg, f.body.e1), args):
                for e2 in optimized_flatmap(xs.e, ELambda(f.arg, f.body.e2), args):
                    for e in optimized_sum(EBinOp(e1, "+", e2).with_type(e1.type), args):
                        yield e
        # sum flatMap(R, \r -> map(S, \s -> g(r, s))) == sum flatMap(S, \s -> map(R, \r -> g(r, s)))
        if isinstance(f.body, EMap) and inplace_opt:
            R = xs.e
            r = f.arg
            S = f.body.e
            s = f.body.transform_function.arg
            g = f.body.transform_function.body
            for e in optimized_flatmap(S, ELambda(s, EMap(R, ELambda(r, g)).with_type(type(R.type)(g.type))), args):
                for e2 in optimized_sum(e, args, inplace_opt=False):
                    yield e2
    yield sum_of(xs)

def optimized_flatmap(xs, f, args):
    res_type = type(xs.type)(f.body.type)
    res_type = res_type.elem_type
    if isinstance(xs, EStateVar) and not any(v in args for v in free_vars(f)):
        yield EStateVar(EFlatMap(xs.e, f).with_type(res_type)).with_type(res_type)
    if isinstance(xs, EBinOp):
        if xs.op in ("+", "-"):
            for a in optimized_flatmap(xs.e1, f, args):
                for b in optimized_flatmap(xs.e2, f, args):
                    yield EBinOp(a, xs.op, b).with_type(res_type)
    yield EFlatMap(xs, f).with_type(res_type)

def optimized_the(xs, args):
    t = xs.type.elem_type
    if isinstance(xs, ECond):
        for e1 in optimized_the(xs.then_branch, args):
            for e2 in optimized_the(xs.else_branch, args):
                yield optimized_cond(xs.cond, e1, e2)
    if isinstance(xs, EStateVar):
        yield statevar(EUnaryOp(UOp.The, xs.e), t)
    if isinstance(xs.type, TList):
        x = excluded_element(xs, args)
        if x is not None:
            bag, x = x
            for elem in optimized_the(bag, args):
                yield optimized_cond(EEq(elem, x), EListGet(bag, ONE).with_type(t), elem)
    if isinstance(xs, EMap):
        exists = optimized_exists(xs.e)
        for x in optimized_the(xs.e, args):
            yield optimized_cond(exists, xs.transform_function.apply_to(x), construct_value(t))
    if isinstance(xs, EBinOp) and xs.op == "+":
        e1_exists = optimized_exists(xs.e1)
        for x in optimized_the(xs.e1, args):
            for y in optimized_the(xs.e2, args):
                yield optimized_cond(e1_exists, x, y)
    yield EUnaryOp(UOp.The, xs).with_type(t)

def optimized_distinct(xs, args):
    if isinstance(xs, EEmptyList) or isinstance(xs, ESingleton):
        yield xs
        return
    if isinstance(xs, EStateVar):
        yield statevar(EUnaryOp(UOp.Distinct, xs.e), xs.type)
    if isinstance(xs, EBinOp):
        if xs.op == "+":
            v = fresh_var(xs.type.elem_type)
            for a in optimized_distinct(xs.e1, args):
                for b in optimized_distinct(xs.e2, args):
                    for b_prime in optimized_filter(b, ELambda(v, ENot(optimized_in(v, a))), args):
                        yield EBinOp(a, "+", b_prime).with_type(xs.type)
        if xs.op == "-":
            v = fresh_var(xs.type.elem_type)
            for a in optimized_distinct(xs.e1, args):
                for b in optimized_distinct(xs.e2, args):
                    yield from optimized_filter(a, ELambda(v, ENot(optimized_in(v, b))), args)
    if isinstance(xs, EFilter):
        for ee in optimized_distinct(xs.e, args):
            yield EFilter(ee, xs.predicate).with_type(xs.type)
    yield EUnaryOp(UOp.Distinct, xs).with_type(xs.type)

def fold_into_map(e, context):
    fvs = free_vars(e)
    state_vars = [v for v, p in context.vars() if p == STATE_POOL]
    for subexp, subcontext, subpool in all_subexpressions_with_context_information(e, context, RUNTIME_POOL):
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
            new_map = map_values(map, func.apply_to)
            yield EMapGet(EStateVar(new_map).with_type(new_map.type), key).with_type(e.type)
