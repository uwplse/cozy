import itertools

from cozy.common import find_one, partition, pick_to_sum, unique
from cozy.target_syntax import *
from cozy.syntax_tools import fresh_var, free_vars, break_conj, pprint, enumerate_fragments, mk_lambda, strip_EStateVar, alpha_equivalent, subst, break_sum, replace, compose
from cozy.typecheck import is_numeric, is_collection
from cozy.pools import RUNTIME_POOL, STATE_POOL, ALL_POOLS, pool_name
from cozy.simplification import simplify
from cozy.enumeration import AuxBuilder
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
            ECond(optimized_in(xs.e2.e, xs.e1), ONE, ZERO).with_type(INT)).with_type(INT)
    else:
        return ELen(EFilter(xs, mk_lambda(x.type, lambda y: EEq(x, y))).with_type(xs.type)).with_type(INT)

def optimized_in(x, xs):
    if isinstance(xs, EStateVar):
        m = EMakeMap2(xs.e, mk_lambda(x.type, lambda x: T)).with_type(TMap(x.type, BOOL))
        m = EStateVar(m).with_type(m.type)
        return EHasKey(m, x).with_type(BOOL)
    elif isinstance(xs, EBinOp) and xs.op == "-" and isinstance(xs.e1, EStateVar) and isinstance(xs.e2, ESingleton):
        return ECond(EEq(x, xs.e2.e),
            EGt(optimized_count(x, xs.e1), ONE),
            optimized_in(x, xs.e1)).with_type(BOOL)
    elif isinstance(xs, EBinOp) and xs.op == "-":
        return EGt(optimized_count(x, xs.e1), optimized_count(x, xs.e2))
    elif isinstance(xs, ECond):
        return ECond(xs.cond,
            optimized_in(x, xs.then_branch),
            optimized_in(x, xs.else_branch)).with_type(BOOL)
    elif isinstance(xs, EFilter):
        return EAll([xs.p.apply_to(x), optimized_in(x, xs.e)])
    else:
        return EBinOp(x, BOp.In, xs).with_type(BOOL)

def optimized_len(xs):
    if isinstance(xs, EStateVar):
        return EStateVar(optimized_len(xs.e)).with_type(INT)
    elif isinstance(xs, EBinOp) and xs.op == "-" and isinstance(xs.e2, ESingleton):
        return EBinOp(
            optimized_len(xs.e1), "-",
            ECond(optimized_in(xs.e2.e, xs.e1), ONE, ZERO).with_type(INT)).with_type(INT)
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
    return EEq(l, ZERO)

def optimized_exists(xs):
    l = optimized_len(xs)
    if isinstance(l, ENum):
        return F if l.val == 0 else T
    return EGt(l, ZERO)

def optimized_best(xs, keyfunc, op, args):
    argbest = EArgMin if op == "<" else EArgMax
    elem_type = xs.type.t
    if isinstance(xs, EEmptyList):
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
    else:
        return argbest(xs, keyfunc).with_type(elem_type)

def optimized_cond(c, a, b):
    if c == T:
        return a
    elif c == F:
        return b
    else:
        return ECond(c, a, b).with_type(a.type)

def _simple_filter(xs, p, args):
    if isinstance(xs, EStateVar) and not any(v in args for v in free_vars(p)):
        return EStateVar(_simple_filter(xs.e, p, args)).with_type(xs.type)
    elif isinstance(p.body, EBinOp) and p.body.op == "==" and p.body.e1 == p.arg and p.arg not in free_vars(p.body.e2):
        return optimized_cond(
            optimized_in(p.body.e2, xs),
            ESingleton(p.body.e2).with_type(xs.type),
            EEmptyList().with_type(xs.type)).with_type(xs.type)
    else:
        return EFilter(xs, p).with_type(xs.type)

def optimize_filter_as_if_distinct(xs, p, args):
    from cozy.syntax_tools import dnf
    cases = dnf(p.body)
    for c in cases:
        print("; ".join(pprint(x) for x in c))
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
    if isinstance(f.body, ECond):
        return EBinOp(
            optimize_map(optimize_filter_as_if_distinct(xs, ELambda(f.arg,      f.body.cond) , args=args), ELambda(f.arg, f.body.then_branch), args), "+",
            optimize_map(optimize_filter_as_if_distinct(xs, ELambda(f.arg, ENot(f.body.cond)), args=args), ELambda(f.arg, f.body.else_branch), args)).with_type(res_type)
    else:
        return EMap(xs, f).with_type(res_type)

class accelerate_build(AuxBuilder):
    def __init__(self, build_candidates, args, state_vars):
        super().__init__(build_candidates)
        self.args = args
        self.state_vars = state_vars
    def check(self, e, pool):
        # print("  --> trying {}".format(pprint(e)))
        return (e, pool)
    def apply(self, cache, size, scopes, build_lambdas, e, pool):
        if not accelerate.value:
            return
        # print("accelerating {} [in {}]".format(pprint(e), pool_name(pool)))
        ee = simplify(e)
        if not alpha_equivalent(ee, e):
            yield self.check(simplify(e), pool)
        if pool == RUNTIME_POOL:
            if all(v in self.state_vars for v in free_vars(e)):
                nsv = strip_EStateVar(e)
                sv = EStateVar(nsv).with_type(e.type)
                yield self.check(sv, RUNTIME_POOL)
                yield self.check(nsv, STATE_POOL)

            yield from map_accelerate(e, self.state_vars, self.args, cache, size-1)

            # xs - (xs - [i])
            # ===> (i in xs) ? [i] : []
            if is_collection(e.type) and isinstance(e, EBinOp) and e.op == "-" and isinstance(e.e2, EBinOp) and e.e2.op == "-" and isinstance(e.e2.e2, ESingleton) and alpha_equivalent(e.e1, e.e2.e1):
                e = ECond(optimized_in(e.e2.e2.e, e.e1),
                    e.e2.e2,
                    EEmptyList().with_type(e.type)).with_type(e.type)
                yield self.check(e, RUNTIME_POOL)
                yield self.check(e.cond, RUNTIME_POOL)

            # [x] - xs
            if is_collection(e.type) and isinstance(e, EBinOp) and e.op == "-" and isinstance(e.e1, ESingleton):
                e = ECond(
                    optimized_in(e.e1.e, e.e2),
                    EEmptyList().with_type(e.type),
                    e.e1).with_type(e.type)
                yield self.check(e, RUNTIME_POOL)
                yield self.check(e.cond, RUNTIME_POOL)

            if isinstance(e, EBinOp) and e.op == BOp.In:
                ee = optimized_in(e.e1, e.e2)
                if not alpha_equivalent(e, ee):
                    yield self.check(ee, RUNTIME_POOL)

            if isinstance(e, EUnaryOp) and e.op == UOp.Empty:
                ee = optimized_empty(e.e)
                if not alpha_equivalent(e, ee):
                    yield self.check(ee, RUNTIME_POOL)

            if isinstance(e, EUnaryOp) and e.op == UOp.Exists:
                ee = optimized_exists(e.e)
                if not alpha_equivalent(e, ee):
                    yield self.check(ee, RUNTIME_POOL)

            if isinstance(e, EUnaryOp) and e.op == UOp.Length:
                ee = optimized_len(e.e)
                if not alpha_equivalent(e, ee):
                    yield self.check(ee, RUNTIME_POOL)

            if isinstance(e, EArgMin) or isinstance(e, EArgMax):
                ee = optimized_best(e.e, e.f, "<" if isinstance(e, EArgMin) else ">", args=self.args)
                if not alpha_equivalent(e, ee):
                    yield self.check(ee, RUNTIME_POOL)

            if isinstance(e, EFilter):
                ee = optimize_filter_as_if_distinct(e.e, e.p, args=self.args)
                if not alpha_equivalent(e, ee):
                    yield self.check(ee, RUNTIME_POOL)

            if isinstance(e, EMap):
                ee = optimize_map(e.e, e.f, args=self.args)
                if not alpha_equivalent(e, ee):
                    yield self.check(ee, RUNTIME_POOL)

            # {min,max} (xs - [i])
            if (isinstance(e, EArgMin) or isinstance(e, EArgMax)) and isinstance(e.e, EBinOp) and e.e.op == "-" and isinstance(e.e.e1, EStateVar) and isinstance(e.e.e2, ESingleton):
                heap_type, make_heap = (TMinHeap, EMakeMinHeap) if isinstance(e, EArgMin) else (TMaxHeap, EMakeMaxHeap)
                bag = e.e.e1
                x = e.e.e2.e
                h = make_heap(bag.e, e.f).with_type(heap_type(e.e.type.t, e.f))
                prev_min = EStateVar(type(e)(bag.e, e.f).with_type(e.type)).with_type(e.type)
                e = ECond(
                    EAll([optimized_in(x, bag), EEq(x, prev_min)]),
                    EHeapPeek2(EStateVar(h).with_type(h.type), EStateVar(ELen(bag.e)).with_type(INT)).with_type(e.type),
                    prev_min).with_type(e.type)
                yield self.check(e, RUNTIME_POOL)

            # EStateVar(distinct xs) - (EStateVar(xs) - [i])
            # ===> is-last(i, xs) ? [] : [i]
            if (is_collection(e.type) and
                    isinstance(e, EBinOp) and e.op == "-" and
                    isinstance(e.e2, EBinOp) and e.e2.op == "-" and
                    isinstance(e.e2.e1, EStateVar) and
                    isinstance(e.e2.e2, ESingleton) and
                    isinstance(e.e1, EStateVar) and isinstance(e.e1.e, EUnaryOp) and e.e1.e.op == UOp.Distinct and
                    alpha_equivalent(e.e1.e.e, e.e2.e1.e)):
                distinct_elems = e.e1.e
                elems = distinct_elems.e
                elem_type = elems.type.t
                m = histogram(elems)
                m_rt = EStateVar(m).with_type(m.type)
                count = EMapGet(m_rt, e.e2.e2.e).with_type(INT)
                e = ECond(
                    EEq(count, ONE),
                    e.e2.e2,
                    EEmptyList().with_type(e.type)).with_type(e.type)
                yield self.check(e, RUNTIME_POOL)
                yield self.check(e.cond, RUNTIME_POOL)
                yield self.check(m, STATE_POOL)
                yield self.check(m_rt, RUNTIME_POOL)
