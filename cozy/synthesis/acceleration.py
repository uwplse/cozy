import itertools

from cozy.common import find_one, partition, pick_to_sum
from cozy.target_syntax import *
from cozy.syntax_tools import fresh_var, free_vars, break_conj, pprint, enumerate_fragments, mk_lambda, strip_EStateVar, alpha_equivalent, subst, break_sum, replace
from cozy.typecheck import is_numeric, is_collection
from cozy.pools import RUNTIME_POOL, STATE_POOL, ALL_POOLS
from cozy.simplification import simplify
from cozy.enumeration import AuxBuilder

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
        keys = EUnion([reachable_values_of_type(v, arg.type) for v in state_vars]).with_type(TBag(arg.type))
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
    else:
        return EBinOp(x, BOp.In, xs).with_type(BOOL)

def optimized_len(xs):
    if isinstance(xs, EStateVar):
        return EStateVar(ELen(xs.e)).with_type(INT)
    elif isinstance(xs, EBinOp) and xs.op == "-" and isinstance(xs.e2, ESingleton):
        return EBinOp(
            optimized_len(xs.e1), "-",
            ECond(optimized_in(xs.e2.e, xs.e1), ONE, ZERO).with_type(INT)).with_type(INT)
    else:
        return ELen(xs)

def optimized_empty(xs):
    return EEq(optimized_len(xs), ZERO)

def optimized_exists(xs):
    return EGt(optimized_len(xs), ZERO)

class accelerate_build(AuxBuilder):
    def __init__(self, build_candidates, args, state_vars):
        super().__init__(build_candidates)
        self.args = args
        self.state_vars = state_vars
    def apply(self, cache, size, scopes, build_lambdas, e, pool):
        if not accelerate.value:
            return
        yield (simplify(e), pool)
        if pool == RUNTIME_POOL:
            yield from map_accelerate(e, self.state_vars, self.args, cache, size-1)

            # xs - (xs - [i])
            # ===> (i in xs) ? [i] : []
            if is_collection(e.type) and isinstance(e, EBinOp) and e.op == "-" and isinstance(e.e2, EBinOp) and e.e2.op == "-" and isinstance(e.e2.e2, ESingleton) and alpha_equivalent(e.e1, e.e2.e1):
                e = ECond(optimized_in(e.e2.e2.e, e.e1),
                    e.e2.e2,
                    EEmptyList().with_type(e.type)).with_type(e.type)
                yield (e, RUNTIME_POOL)
                yield (e.cond, RUNTIME_POOL)

            if isinstance(e, EBinOp) and e.op == BOp.In:
                ee = optimized_in(e.e1, e.e2)
                if not alpha_equivalent(e, ee):
                    yield (ee, RUNTIME_POOL)

            if isinstance(e, EUnaryOp) and e.op == UOp.Empty:
                ee = optimized_empty(e.e)
                if not alpha_equivalent(e, ee):
                    yield (ee, RUNTIME_POOL)

            if isinstance(e, EUnaryOp) and e.op == UOp.Exists:
                ee = optimized_exists(e.e)
                if not alpha_equivalent(e, ee):
                    yield (ee, RUNTIME_POOL)

            if isinstance(e, EUnaryOp) and e.op == UOp.Length:
                ee = optimized_len(e.e)
                if not alpha_equivalent(e, ee):
                    yield (ee, RUNTIME_POOL)

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
                yield (e, RUNTIME_POOL)
                yield (e.cond, RUNTIME_POOL)
                yield (m, STATE_POOL)
                yield (m_rt, RUNTIME_POOL)
