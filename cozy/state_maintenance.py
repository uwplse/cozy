"""Functions for managing stateful computation.

Important functions:
 - mutate: compute the new value of an expression after a statement executes
 - mutate_in_place: write code to keep a derived value in sync with its inputs
"""

import itertools
from collections import OrderedDict
import functools

from cozy.common import fresh_name, typechecked, find_one, unique
from cozy import syntax
from cozy import target_syntax
from cozy.syntax_tools import free_vars, free_funcs, pprint, fresh_var, strip_EStateVar, subst, BottomUpRewriter, alpha_equivalent, break_seq, break_sum, mk_lambda, qsubst
from cozy.syntax_tools import break_conj
from cozy.syntax_tools import cse, freshen_binders
from cozy.syntax_tools import qsubst
from cozy.typecheck import is_numeric, is_collection, retypecheck
from cozy.solver import valid, ModelCachingSolver
from cozy.opts import Option
from cozy.structures import extension_handler
from cozy.evaluation import construct_value, eval, uneval
from cozy.contexts import Context, UnderBinder
from cozy.pools import STATE_POOL, RUNTIME_POOL
from cozy.simplification import simplify, simplify_cond as cond
from cozy.wf import exp_wf
from cozy.logging import task, verbose

skip_stateless_synthesis = Option("skip-stateless-synthesis", bool, False,
    description="Do not waste time optimizing expressions that do not depend on the data structure state")
update_numbers_with_deltas = Option("update-numbers-with-deltas", bool, False)

def mutate(e : syntax.Exp, op : syntax.Stm) -> syntax.Exp:
    """Return the new value of `e` after executing `op`."""
    if isinstance(op, syntax.SNoOp):
        return e
    elif isinstance(op, syntax.SAssign):
        return _do_assignment(op.lhs, op.rhs, e)
    elif isinstance(op, syntax.SCall):
        if op.func == "add":
            return mutate(e, syntax.SCall(op.target, "add_all", (syntax.ESingleton(op.args[0]).with_type(op.target.type),)))
        elif op.func == "add_all":
            return mutate(e, syntax.SAssign(op.target, syntax.EBinOp(op.target, "+", op.args[0]).with_type(op.target.type)))
        elif op.func == "remove":
            return mutate(e, syntax.SCall(op.target, "remove_all", (syntax.ESingleton(op.args[0]).with_type(op.target.type),)))
        elif op.func == "remove_all":
            return mutate(e, syntax.SAssign(op.target, syntax.EBinOp(op.target, "-", op.args[0]).with_type(op.target.type)))
        else:
            raise Exception("Unknown func: {}".format(op.func))
    elif isinstance(op, syntax.SIf):
        then_branch = mutate(e, op.then_branch)
        else_branch = mutate(e, op.else_branch)
        if alpha_equivalent(then_branch, else_branch):
            return then_branch
        return syntax.ECond(op.cond, then_branch, else_branch).with_type(e.type)
    elif isinstance(op, syntax.SSeq):
        if isinstance(op.s1, syntax.SSeq):
            return mutate(e, syntax.SSeq(op.s1.s1, syntax.SSeq(op.s1.s2, op.s2)))
        e2 = mutate(mutate(e, op.s2), op.s1)
        if isinstance(op.s1, syntax.SDecl):
            e2 = qsubst(e2, syntax.EVar(op.s1.id).with_type(op.s1.val.type), op.s1.val)
            # e2 = subst(e2, { op.s1.id : op.s1.val })
        return e2
    elif isinstance(op, syntax.SDecl):
        return e
    else:
        raise NotImplementedError(type(op))

def simplify_white(s):
    s = s.strip()
    s = s.replace("\n", " ")
    s = s.replace(r"\s+", " ")
    return s

### No, bad idea: between the decl and its use, the vars it mentions may change
# def inline_sdecl(s, env=None):
#     if env is None:
#         env = { }
#     if isinstance(s, syntax.SNoOp):
#         return s
#     if isinstance(s, syntax.SSeq):
#         s1 = inline_sdecl(s.s1, env)
#         s2 = inline_sdecl(s.s2, env)
#         return syntax.SSeq(s1, s2)
#     if isinstance(s, syntax.SIf):
#         return syntax.SIf(
#             subst(s.cond, env),
#             inline_sdecl(s.then_branch, dict(env)),
#             inline_sdecl(s.else_branch, dict(env)))
#     if isinstance(s, syntax.SCall):
#         return syntax.SCall(s.target, s.func, tuple(subst(a, env) for a in s.args))
#     if isinstance(s, syntax.SAssign):
#         return syntax.SAssign(s.lhs, subst(s.rhs, env))
#     if isinstance(s, syntax.SDecl):
#         env[s.id] = subst(s.val, env)
#         return syntax.SNoOp()
#     raise NotImplementedError(type(s))

def differences(e1, e2):
    from cozy.common import ADT
    if isinstance(e1, syntax.ELambda):
        return
    if isinstance(e1, ADT) and type(e1) is type(e2):
        for c1, c2 in zip(e1.children(), e2.children()):
            yield from differences(c1, c2)
    yield e1, e2

@typechecked
def assert_eq(e1 : syntax.Exp, e2 : syntax.Exp, context : Context, assumptions : syntax.Exp = syntax.T):
    formula = syntax.EAll([assumptions, syntax.ENot(syntax.EEq(e1, e2))])
    model = minimal_model(formula)
    if model is not None:
        from cozy.evaluation import eval
        from cozy.contexts import shred
        from cozy.common import unique

        fvs = free_vars(formula)
        pprint_model(model, { v.id : v.type for v in fvs })
        # print("--->")
        # for v in fvs:
        #     print("  {} = {}".format(v.id, pprint_value(v.type, eval(mutate(v, op), model))))

        import itertools
        for x1, x2 in unique(itertools.chain([(e1, e2)], differences(e1, e2))):

            print("=" * 20)

            print(pprint(x1))
            print(pprint(x2))

            print("expected: {}".format(pprint_value(x1.type, eval(x1, model))))
            print("got: {}".format(pprint_value(x2.type, eval(x2, model))))

            # for x, x_ctx, _ in unique(shred(e2, context)):
            #     if x_ctx == context:
            #         print("=" * 20)
            #         print("{} ----> {}".format(pprint(x), pprint_value(x.type, eval(x, model))))

        raise AssertionError()

def statevar(e):
    return target_syntax.EStateVar(e).with_type(e.type)

@typechecked
def better_mutate(
        e           : target_syntax.EStateVar,
        context     : Context,
        op          : syntax.Stm,
        assumptions : syntax.Exp = syntax.T) -> syntax.Exp:
    """
    NOTES
        - e is runtime exp
        - output is runtime exp
    """
    # print("{} X {}".format(pprint(e), simplify_white(pprint(op))))

    if alpha_equivalent(e.e, mutate(e.e, op)):
        return e

    # special case on the structure of e
    esv = e
    e = e.e

    if isinstance(e.type, syntax.TBag) or isinstance(e.type, syntax.TSet):
        add, remove = bag_delta(e, context, op, assumptions)
        print("{} x {} ---> +{}, -{}".format(pprint(e), pprint(op), pprint(add), pprint(remove)))
        return bag_union(bag_subtract(esv, remove), add)

    if isinstance(e, syntax.EUnaryOp):
        if e.op == syntax.UOp.Exists:
            add, remove = bag_delta(e.e, context, op, assumptions)
            return syntax.EGt(
                statevar(len_of(e.e)) + len_of(add),
                len_of(remove))
        if e.op == syntax.UOp.Not:
            new_val = better_mutate(statevar(e.e), context, op, assumptions)
            return syntax.ENot(new_val)

    if isinstance(e, syntax.ESingleton):
        return syntax.ESingleton(
            better_mutate(statevar(e.e), context, op)).with_type(e.type)

    if isinstance(e, syntax.EBinOp):
        return syntax.EBinOp(
            better_mutate(statevar(e.e1), context, op, assumptions), e.op,
            better_mutate(statevar(e.e2), context, op, assumptions)).with_type(e.type)

    if isinstance(e, syntax.ECall):
        return syntax.ECall(e.func,
            tuple(better_mutate(statevar(x), context, op, assumptions) for x in e.args)).with_type(e.type)

    if isinstance(e, syntax.ECond):
        then_branch = better_mutate(statevar(e.then_branch), context, op, assumptions)
        else_branch = better_mutate(statevar(e.else_branch), context, op, assumptions)
        return cond(e.cond,
            cond(became_false(e.cond, context, op, assumptions), else_branch, then_branch),
            cond(became_true (e.cond, context, op, assumptions), then_branch, else_branch))

    # if bag:
    #     added+removed
    if isinstance(e, syntax.EArgMin) or isinstance(e, syntax.EArgMax):
        if alpha_equivalent(e.f, mutate(e.f, op)):

            to_add, to_del = bag_delta(e.e, context, op, assumptions)
            # to_del, to_add = (
            #     bag_subtract(to_del, to_add),
            #     bag_subtract(to_add, to_del))

            # print("Simplifying...")
            # to_del = partial_eval(to_del)
            # to_add = partial_eval(to_add)

            # print("Final delta:")
            # print(" - {}".format(pprint(to_del)))
            # print(" + {}".format(pprint(to_add)))

            from cozy.structures.heaps import to_heap, EHeapPeek2
            h = to_heap(e)
            h = statevar(h)
            second_min = syntax.ESingleton(EHeapPeek2(h, statevar(syntax.ELen(e.e))).with_type(e.type)).with_type(e.e.type)

            # v = fresh_var(to_del.type, "removed")
            # if isinstance(to_del, syntax.EEmptyList) or valid(syntax.EImplies(assumptions, syntax.EEmpty(to_del))):
            #     min_after_del = esv
            # elif valid(syntax.EImplies(assumptions, syntax.EEq(syntax.ELen(to_del), syntax.ONE))):
            #     min_after_del = second_min
            # print("Checking for efficient removal...")
            # if valid(syntax.EImplies(assumptions, syntax.EEmpty(to_del))):
            #     min_after_del = syntax.ESingleton(esv).with_type(e.e.type)
            # elif valid(syntax.EImplies(assumptions, syntax.ELe(syntax.ELen(to_del), syntax.ONE))):
            #     min_after_del = syntax.ECond(
            #         syntax.ELet(
            #             to_del,
            #             syntax.ELambda(v,
            #                 syntax.EAll([syntax.EExists(v), syntax.EEq(syntax.EUnaryOp(syntax.UOp.The, v).with_type(e.type), esv)]))).with_type(syntax.BOOL),
            #         syntax.ECond(syntax.EGt(target_syntax.EStateVar(syntax.ELen(e.e)).with_type(syntax.INT), syntax.ONE), second_min, syntax.EEmptyList().with_type(e.e.type)).with_type(e.e.type),
            #         syntax.ECond(target_syntax.EStateVar(syntax.EExists(e.e)).with_type(syntax.BOOL), syntax.ESingleton(esv).with_type(e.e.type), syntax.EEmptyList().with_type(e.e.type)).with_type(e.e.type)).with_type(e.e.type)
            #     assert_eq(
            #         type(e)(bag_subtract(e.e, to_del), e.f).with_type(e.type),
            #         type(e)(min_after_del, e.f).with_type(e.type),
            #         context=context,
            #         assumptions=assumptions)
            # else:
            #     # ugh, recompute
            #     print("assuming {}".format(pprint(assumptions)))
            #     print("deleting {}".format(pprint(to_del)))
            #     model = minimal_model(syntax.EAll([assumptions, syntax.ENot(syntax.ELe(syntax.ELen(to_del), syntax.ONE))]), solver=solver_for(context))
            #     print("Ooops!")
            #     print("  assuming {}".format(pprint(assumptions)))
            #     print("  e.type is {}".format(pprint(e.type)))
            #     print("  d  = {}".format(pprint(to_del)))
            #     print("  n  = {}".format(pprint(to_add)))
            #     print("del         : {}".format(eval(to_del, model)))
            #     print("add         : {}".format(eval(to_add, model)))
            #     print("true del    : {}".format(eval(to_bag(e.e) - to_bag(mutate(e.e, op)), model)))
            #     print("true add    : {}".format(eval(to_bag(mutate(e.e, op)) - to_bag(e.e), model)))
            #     raise NotEfficient(e)
            #     return mutate(e, op)

            # add_min = type(e)(to_add, e.f).with_type(e.type)

            # res = type(e)(bag_union(
            #     min_after_del,
            #     to_add), e.f).with_type(e.type)

            # res = cond(statevar(exists(e.e)),
            #     res,
            #     add_min)


            del_var = fresh_var(to_del.type, "removed")
            add_var = fresh_var(to_add.type, "added")

            add_min = type(e)(add_var, e.f).with_type(e.type)
            added_bag = cond(
                exists(add_var),
                syntax.ESingleton(add_min).with_type(syntax.TBag(add_min.type)),
                syntax.EEmptyList().with_type(syntax.TBag(add_min.type)))

            min_before_del = cond(
                statevar(exists(e.e)),
                syntax.ESingleton(esv).with_type(syntax.TBag(esv.type)),
                syntax.EEmptyList().with_type(syntax.TBag(esv.type)))

            after_del = bag_subtract(e.e, del_var)
            recompute = cond(exists(after_del),
                syntax.ESingleton(type(e)(after_del, e.f).with_type(e.type)).with_type(syntax.TBag(esv.type)),
                syntax.EEmptyList().with_type(syntax.TBag(esv.type)))
            min_after_del = cond(exists(del_var),
                cond(syntax.EEq(len_of(del_var), syntax.ONE),
                    cond(syntax.EEq(syntax.EUnaryOp(syntax.UOp.The, del_var).with_type(e.type), esv), second_min, min_before_del),
                    recompute),
                min_before_del)

            res = type(e)(bag_union(
                min_after_del,
                added_bag), e.f).with_type(e.type)

            res = qsubst(res, add_var, bag_subtract(to_add, to_del))
            res = qsubst(res, del_var, bag_subtract(to_del, to_add))

            assert retypecheck(res)
            return res

    # # take care of basic statement forms
    # if isinstance(op, syntax.SNoOp):
    #     return e
    # if isinstance(op, syntax.SSeq):
    #     e = better_mutate(e, context, op.s1)
    #     e = better_mutate_statevars(e, context, op.s2)
    #     return e
    # if isinstance(op, syntax.SIf):
    #     return syntax.ECond(
    #         op.cond,
    #         better_mutate(e, context, op.then_branch),
    #         better_mutate(e, context, op.else_branch)).with_type(e.type)
    # if isinstance(op, syntax.SDecl):
    #     raise ValueError()

    # print("e = {!r}".format(e))
    # print("context = {!r}".format(context))
    # print("op = {!r}".format(op))
    # print("env = {!r}".format(env))
    print(pprint(e))
    print(pprint(op))
    raise NotImplementedError(pprint(e))

# def invert(f : syntax.ELambda, domain : syntax.Exp) -> syntax.ELambda:
#     """Invert f over the given domain."""
#     raise NotImplementedError(pprint(f))

from cozy.syntax_tools import compose

def require_equal(spec):
    def wrapper(f):

        @functools.wraps(f)
        def wrapped(*args, **kwargs):
            res = f(*args, **kwargs)
            x = spec(*args, **kwargs).with_type(res.type)
            assert res.type == x.type
            # assert not (free_vars(res) - free_vars(x)), "{f}({args}) = {res!r}".format(f=f.__name__, args=", ".join(repr(a) for a in args), res=res)
            return res
            # return x
            model = minimal_model(syntax.ENot(syntax.EEq(res, x)))
            if model is not None:
                print("{} misbehaved!".format(f))
                print("input: {}".format("; ".join(pprint(e) for e in args)))
                print("output: {}".format(pprint(res)))
                print(" - expected: {}".format(eval(x, model)))
                print(" - got: {}".format(eval(res, model)))
            return res

        return wrapped
    return wrapper

@typechecked
def apply(f : syntax.ELambda, arg : syntax.Exp) -> syntax.Exp:
    assert arg.type == f.arg.type
    return qsubst(f.body, f.arg, arg)

@require_equal(lambda e, f: target_syntax.EMap(e, f).with_type(type(e.type)(f.body.type)))
def emap(e, f):
    if f.body == f.arg:
        return e
    out_type = type(e.type)(f.body.type)
    if isinstance(e, syntax.EEmptyList):
        return syntax.EEmptyList().with_type(out_type)
    if isinstance(e, syntax.ESingleton):
        return syntax.ESingleton(apply(f, e.e)).with_type(out_type)
    if isinstance(e, syntax.ELet) and e.f.arg not in free_vars(f):
        return qsubst(emap(e.f.body, f), e.f.arg, e.e)
    # if isinstance(e, syntax.EBinOp) and e.op == "+":
    #     return bag_union(emap(e.e1, f), emap(e.e2, f))
    # if isinstance(e, target_syntax.EMap):
    #     return emap(e.e, compose(f, e.f))
    if isinstance(e, syntax.ECond):
        return cond(e.cond,
            emap(e.then_branch, f),
            emap(e.else_branch, f))
    return target_syntax.EMap(e, f).with_type(out_type)

@require_equal(lambda e, f: target_syntax.EFilter(e, f).with_type(e.type))
def efilter(e, f):
    if f.body == syntax.T:
        return e
    if f.body == syntax.F:
        return syntax.EEmptyList().with_type(e.type)
    out_type = e.type
    if isinstance(e, syntax.EEmptyList):
        return syntax.EEmptyList().with_type(out_type)
    if isinstance(e, syntax.ELet) and e.f.arg not in free_vars(f):
        return qsubst(efilter(e.f.body, f), e.f.arg, e.e)
    # if isinstance(e, syntax.EBinOp) and e.op == "+":
    #     return bag_union(efilter(e.e1, f), efilter(e.e2, f))
    # if isinstance(e, syntax.EBinOp) and e.op == "-":
    #     return bag_subtract(efilter(e.e1, f), efilter(e.e2, f))
    # if isinstance(e, syntax.EBinOp) and e.op == "intersect":
    #     return bag_intersection(efilter(e.e1, f), efilter(e.e2, f))
    # if isinstance(e, target_syntax.EMap):
    #     return efilter(e.e, compose(f, e.f))
    if isinstance(e, syntax.ESingleton):
        return cond(
            apply(f, e.e),
            e,
            syntax.EEmptyList().with_type(e.type))
    if isinstance(e, syntax.ECond):
        return cond(
            e.cond,
            efilter(e.then_branch, f),
            efilter(e.else_branch, f))
    return target_syntax.EFilter(e, f).with_type(out_type)

def countin(x, bag):
    # return target_syntax.ECountIn(x, bag)
    return len_of(efilter(bag, mk_lambda(x.type, lambda y: equal(x, y))))

def is_filter(f_arg, f_body):
    if isinstance(f_body, syntax.ECond):
        return both(
            is_filter(f_arg, f_body.then_branch),
            is_filter(f_arg, f_body.else_branch))
    if isinstance(f_body, syntax.EEmptyList):
        return True
    if isinstance(f_body, syntax.ESingleton) and f_body.e == f_arg:
        return True
    return MAYBE

def to_predicate(f_body):
    # PRE: is_filter(?, f_body)
    if isinstance(f_body, syntax.ECond):
        return cond(f_body.cond,
            to_predicate(f_body.then_branch),
            to_predicate(f_body.else_branch))
    if isinstance(f_body, syntax.EEmptyList):
        return syntax.F
    if isinstance(f_body, syntax.ESingleton):
        return syntax.T
    raise ValueError(cond)

def infer_the_one_passing_element(f_arg, f_body):
    f_body = nnf(f_body)
    for part in break_conj(f_body):
        print(" * {}".format(pprint(part)))
        if isinstance(part, syntax.EBinOp) and part.op in ("==", "==="):
            for e1, e2 in itertools.permutations([part.e1, part.e2]):
                if e1 == f_arg and f_arg not in free_vars(e2):
                    return e2
    return None

def injective(f):
    if f.arg == f.body:
        return True
    return MAYBE

def are_unique(xs):
    if definitely(singleton_or_empty(xs)):
        return True
    if isinstance(xs, syntax.EUnaryOp) and xs.op == syntax.UOp.Distinct:
        return True
    if isinstance(xs, target_syntax.EFilter):
        return are_unique(xs.e)
    if isinstance(xs, target_syntax.EMap):
        return both(injective(xs.f), are_unique(xs.e))
    if isinstance(xs, syntax.EBinOp) and xs.op == "-":
        return are_unique(xs.e1)
    if isinstance(xs, syntax.ECond):
        return both(are_unique(xs.then_branch), are_unique(xs.else_branch))
    return MAYBE

@require_equal(lambda e, f: target_syntax.EFlatMap(e, f).with_type(f.body.type))
def flatmap(e, f):
    if isinstance(f.body, syntax.ESingleton):
        return emap(e, syntax.ELambda(f.arg, f.body.e))
    if isinstance(f.body, syntax.ECond) and isinstance(f.body.then_branch, syntax.ESingleton) and f.body.then_branch.e == f.arg and isinstance(f.body.else_branch, syntax.EEmptyList):
        return efilter(e, syntax.ELambda(f.arg, f.body.cond))
    if isinstance(e, syntax.EEmptyList) or isinstance(f.body, syntax.EEmptyList):
        return syntax.EEmptyList().with_type(f.body.type)
    if isinstance(e, syntax.ESingleton):
        # return simplify(f.apply_to(e.e))
        return apply(f, e.e)
    # if isinstance(e, syntax.EBinOp) and e.op == "+":
    #     return bag_union(flatmap(e.e1, f), flatmap(e.e2, f))
    if isinstance(e, syntax.ECond):
        return cond(e.cond,
            flatmap(e.then_branch, f),
            flatmap(e.else_branch, f))
    # if definitely(is_filter(f.arg, f.body)):
    #     print("FILTER: {}".format(pprint(f.body)))
    #     if definitely(are_unique(e)):
    #         print("UNIQUE: {}".format(pprint(e)))
    #         x = infer_the_one_passing_element(f.arg, to_predicate(f.body))
    #         if x is not None:
    #             e = syntax.ESingleton(x).with_type(e.type)
    #         else:
    #             raise ValueError(pprint(f.body))
    return target_syntax.EFlatMap(e, f).with_type(f.body.type)

class NotEfficient(Exception):
    def __init__(self, e):
        super().__init__(pprint(e))
        self.expression = e

@require_equal(lambda bag, x: syntax.EIn(x, bag))
def bag_contains(bag, x):
    if definitely(element_of(x, bag)):
        return syntax.T
    if isinstance(bag, target_syntax.EFilter):
        return syntax.EAll([
            bag_contains(bag.e, x),
            apply(bag.p, x)])
    if isinstance(bag, syntax.ESingleton):
        return equal(bag.e, x)
    if isinstance(bag, syntax.EEmptyList):
        return syntax.F
    return syntax.EIn(x, bag)

@require_equal(lambda e1, e2: syntax.EBinOp(e1, "-", e2).with_type(e1.type))
def bag_subtract(e1, e2):
    assert types_equiv(e1.type, e2.type)
    if isinstance(e1, syntax.EEmptyList):
        return e1
    if isinstance(e2, syntax.EEmptyList):
        return e1
    l = list(break_sum(e1))
    dup = find_one(l, lambda x: alpha_equivalent(x, e2))
    if dup is not None:
        l.remove(dup)
        return syntax.EUnion(l, elem_type=e1.type.t)
    if isinstance(e2, syntax.ECond):
        return cond(e2.cond,
            bag_subtract(e1, e2.then_branch),
            bag_subtract(e1, e2.else_branch)).with_type(e1.type)
    if isinstance(e1, syntax.ECond):
        return cond(e1.cond,
            bag_subtract(e1.then_branch, e2),
            bag_subtract(e1.else_branch, e2)).with_type(e1.type)
    # if isinstance(e1, syntax.EBinOp) and e1.op == "+" and alpha_equivalent(e1.e1, e2):
    #     return e1.e2
    # if isinstance(e2, syntax.EBinOp) and e2.op == "+" and alpha_equivalent(e1, e2.e1):
    #     return syntax.EEmptyList().with_type(e1.type)
    if isinstance(e2, syntax.EBinOp) and e2.op == "+":
        return bag_subtract(bag_subtract(e1, e2.e1), e2.e2)
    if isinstance(e1, syntax.EBinOp) and e1.op == "-" and alpha_equivalent(e1.e1, e2):
        return syntax.EEmptyList().with_type(e1.type)
    if isinstance(e2, syntax.EBinOp) and e2.op == "-" and alpha_equivalent(e2.e1, e1) and isinstance(e2.e2, syntax.ESingleton):
        return cond(bag_contains(e1, e2.e2.e), e2.e2, syntax.EEmptyList().with_type(e1.type))
    if isinstance(e2, syntax.EBinOp) and e2.op == "intersect":
        for x, y in [(e2.e1, e2.e2), (e2.e2, e2.e1)]:
            if alpha_equivalent(x, e1):
                return bag_subtract(e1, y)
        raise NotImplementedError(pprint(e1) + " ---- " + pprint(e2))
    # if isinstance(e1, syntax.EBinOp) and e1.op == "+" and isinstance(e1.e2, syntax.ESingleton):
    #     return cond(
    #         bag_contains(e2, e1.e2.e),
    #         bag_subtract(e1.e1, bag_subtract(e2, e1.e2)),
    #         bag_union(bag_subtract(e1.e1, e2), e1.e2.e))
    if isinstance(e1, syntax.ESingleton) and isinstance(e2, syntax.ESingleton):
        return cond(equal(e1.e, e2.e),
            syntax.EEmptyList().with_type(e1.type),
            e1)
    # if isinstance(e2, syntax.ESingleton):
    #     return syntax.EBinOp(e1, "-", e2).with_type(e1.type)
    # raise NotEfficient(syntax.EBinOp(e1, "-", e2).with_type(e1.type))
    return syntax.EBinOp(e1, "-", e2).with_type(e1.type)

@require_equal(lambda e1, e2: syntax.EBinOp(e1, "+", e2).with_type(e1.type))
def bag_union(e1, e2):
    if isinstance(e1, syntax.EEmptyList):
        return e2
    if isinstance(e2, syntax.EEmptyList):
        return e1
    return syntax.EBinOp(e1, "+", e2).with_type(e1.type)

from cozy.syntax_tools import break_ebinop
def break_intersection(e):
    return break_ebinop(e, "intersect")

@require_equal(syntax.EIntersect)
def bag_intersection(e1, e2):
    assert is_collection(e1.type)
    assert is_collection(e2.type)
    assert e1.type.t == e2.type.t
    if isinstance(e1, syntax.EEmptyList):
        return e1
    if isinstance(e2, syntax.EEmptyList):
        return e2
    if isinstance(e1, syntax.ESingleton) and isinstance(e2, syntax.ESingleton):
        return cond(equal(e1.e, e2.e), e1, syntax.EEmptyList().with_type(e1.type))
    if isinstance(e1, syntax.ESingleton):
        return cond(bag_contains(e2, e1.e), e1, syntax.EEmptyList().with_type(e1.type))
    if isinstance(e2, syntax.ESingleton):
        return cond(bag_contains(e1, e2.e), e2, syntax.EEmptyList().with_type(e2.type))
    if any(alpha_equivalent(x, e1) for x in break_sum(e2)):
        return e1
    if any(alpha_equivalent(x, e2) for x in break_sum(e1)):
        return e2
    if any(alpha_equivalent(x, e1) for x in break_intersection(e2)):
        return e2
    if any(alpha_equivalent(x, e2) for x in break_intersection(e1)):
        return e1
    # if isinstance(e1, syntax.ECond):
    #     return cond(e1.cond, bag_intersection(e1.then_branch, e2), bag_intersection(e1.else_branch, e2))
    # if isinstance(e2, syntax.ECond):
    #     return bag_intersection(e2, e1)
    # if isinstance(e1, syntax.EBinOp) and e1.op == "+":
    #     i1 = bag_intersection(e1.e1, e2)
    #     return bag_union(
    #         i1,
    #         bag_intersection(e1.e2, bag_subtract(e2, i1)))
    # raise NotEfficient(syntax.ECall("intersection", (e1, e2)))
    # return bag_subtract(e1, bag_subtract(e1, e2))
    return syntax.EIntersect(e1, e2)

def bag_set_intersection(e1, e2):
    if definitely(are_unique(e1)):
        return bag_intersection(e1, e2)
    return efilter(e1, mk_lambda(e1.type.t, lambda x: bag_contains(e2, x)))

# from collections import namedtuple
# SimpleAssignment = namedtuple("SimpleAssignment", ["lval", "rhs"])

@typechecked
def flatten(s : syntax.Stm, so_far : syntax.Stm = syntax.SNoOp(), pc : syntax.Exp = syntax.T):

    if isinstance(s, syntax.SNoOp) or isinstance(s, syntax.SDecl):
        pass

    elif isinstance(s, syntax.SSeq):
        yield from flatten(s.s1, so_far=so_far, pc=pc)
        yield from flatten(s.s2, so_far=syntax.SSeq(so_far, s.s1), pc=pc)

    elif isinstance(s, syntax.SIf):
        cond = mutate(s.cond, so_far)
        yield from flatten(s.then_branch, so_far=so_far, pc=syntax.EAll([pc, cond]))
        yield from flatten(s.else_branch, so_far=so_far, pc=syntax.EAll([pc, syntax.ENot(cond)]))

    elif isinstance(s, syntax.SCall):
        if s.func == "add":
            yield from flatten(syntax.SCall(s.target, "add_all", (syntax.ESingleton(s.args[0]).with_type(s.target.type),)), so_far=so_far, pc=pc)
        elif s.func == "add_all":
            v = fresh_var(s.target.type.t)
            arg = efilter(mutate(s.args[0], so_far), syntax.ELambda(v, pc))
            yield syntax.SCall(s.target, s.func, (arg,))
        elif s.func == "remove":
            yield from flatten(syntax.SCall(s.target, "remove_all", (syntax.ESingleton(s.args[0]).with_type(s.target.type),)), so_far=so_far, pc=pc)
        elif s.func == "remove_all":
            v = fresh_var(s.target.type.t)
            arg = efilter(mutate(s.args[0], so_far), syntax.ELambda(v, pc))
            yield syntax.SCall(s.target, s.func, (arg,))
        else:
            raise ValueError(s.func)

    elif isinstance(s, syntax.SAssign):
        yield syntax.SAssign(s.lhs, mutate(s.rhs, so_far))

    else:
        raise NotImplementedError(s)


def as_bag(e):
    if isinstance(e.type, syntax.TList):
        elem_type = e.type.t
        return target_syntax.EFilter(e, syntax.ELambda(syntax.EVar("x").with_type(elem_type), syntax.T)).with_type(syntax.TBag(elem_type))
    return e

from contextlib import contextmanager

@contextmanager
def temporarily_extend(l, x):
    old_len = len(l)
    l.extend(x)
    yield
    while len(l) > old_len:
        l.pop()

INFINITY = float("inf")
assert INFINITY == INFINITY

def size_analysis(e, env=None):
    from cozy.common import extend

    if env is None:
        env = { v : (0, INFINITY) for v in free_vars(e) }

    if isinstance(e, syntax.EEmptyList):
        return (0, 0)
    if isinstance(e, syntax.ESingleton):
        return (1, 1)
    if isinstance(e, syntax.EBinOp):
        if e.op == "+":
            min1, max1 = size_analysis(e.e1, env=env)
            min2, max2 = size_analysis(e.e2, env=env)
            return (min1+min2, max1+max2)
        if e.op == "-":
            min1, max1 = size_analysis(e.e1, env=env)
            min2, max2 = size_analysis(e.e2, env=env)

            if min1 == INFINITY and max2 == INFINITY:
                lb = 0
            else:
                lb = max(min1 - max2, 0)

            return (lb, max1)
        if e.op == "intersect":
            min1, max1 = size_analysis(e.e1, env=env)
            min2, max2 = size_analysis(e.e2, env=env)
            return (min(min1, min2), min(max1, max2))
    if isinstance(e, syntax.EUnaryOp) and e.op == syntax.UOp.Distinct:
        lb, ub = size_analysis(e.e, env=env)
        return (min(lb, 1), ub)
    if isinstance(e, syntax.ECond):
        min1, max1 = size_analysis(e.then_branch, env=env)
        min2, max2 = size_analysis(e.else_branch, env=env)
        return (min(min1, min2), max(max1, max2))
    if isinstance(e, target_syntax.EMap):
        return size_analysis(e.e, env=env)
    if isinstance(e, target_syntax.EFilter):
        _, ub = size_analysis(e.e, env=env)
        return (0, ub)
    if isinstance(e, target_syntax.EFlatMap):
        min1, max1 = size_analysis(e.e, env=env)
        with extend(env, e.f.arg, (min1, max1)):
            min2, max2 = size_analysis(e.f.body, env=env)
        return (min1 * min2, max1 * max2)
    if isinstance(e, syntax.ELet):
        if is_collection(e.e.type):
            with extend(env, e.f.arg, size_analysis(e.e, env=env)):
                return size_analysis(e.f.body, env=env)
        else:
            return size_analysis(e.f.body, env=env)
    if isinstance(e, syntax.EVar):
        return env[e]
    if isinstance(e, target_syntax.EStateVar):
        return size_analysis(e.e, env=env)
    raise NotImplementedError(e)

@typechecked
def partial_eval(e : syntax.Exp, assumptions : syntax.Exp = syntax.T) -> syntax.Exp:

    assumptions = list(break_conj(nnf(assumptions)))

    @contextmanager
    def extend_assumptions(cond):
        with temporarily_extend(assumptions, break_conj(nnf(cond))):
            yield

    class V(BottomUpRewriter):

        def visit_EBinOp(self, e):
            if e.op == syntax.BOp.And:
                e1 = self.visit(e.e1)
                with extend_assumptions(e.e1):
                    e2 = self.visit(e.e2)
                return syntax.EAll([e1, e2])
            if e.op == syntax.BOp.Or:
                e1 = self.visit(e.e1)
                with extend_assumptions(syntax.ENot(e.e1)):
                    e2 = self.visit(e.e2)
                return syntax.EAny([e1, e2])
            else:
                e1 = self.visit(e.e1)
                e2 = self.visit(e.e2)

                if e.op == "-":
                    if alpha_equivalent(e1, e2):
                        return syntax.EEmptyList().with_type(e1.type) if is_collection(e1.type) else syntax.ENum(0).with_type(e1.type)
                    if isinstance(e1, syntax.EEmptyList) or isinstance(e2, syntax.EEmptyList):
                        return e1
                if e.op == "+":
                    if isinstance(e1, syntax.EEmptyList):
                        return e2
                    if isinstance(e2, syntax.EEmptyList):
                        return e1
                if e.op == "intersect":
                    lb1, ub1 = size_analysis(e1)
                    lb2, ub2 = size_analysis(e2)

                    if ub1 == 0 or ub2 == 0:
                        return syntax.EEmptyList().with_type(e1.type)

                    if ub1 < INFINITY or ub2 < INFINITY:
                        # print("---")
                        # print("|e1| in [{}, {}]".format(lb1, ub1))
                        # print("|e2| in [{}, {}]".format(lb2, ub2))
                        # print(pprint(e1))
                        # print(pprint(e2))
                        # raise NotImplementedError()
                        pass
                    else:
                        print("---")
                        print("|e1| in [{}, {}]".format(lb1, ub1))
                        print("|e2| in [{}, {}]".format(lb2, ub2))
                        print(pprint(e1))
                        print(pprint(e2))
                        raise NotImplementedError()

                return syntax.EBinOp(e1, e.op, e2).with_type(e.type)

        def visit_EGetField(self, e):
            ee = self.visit(e.e)
            if isinstance(ee, syntax.EMakeRecord):
                return dict(ee.fields)[e.f]
            return syntax.EGetField(ee, e.f).with_type(e.type)

        def visit_ECond(self, e):
            cond = self.visit(e.cond)

            with extend_assumptions(e.cond):
                then_branch = self.visit(e.then_branch)

            with extend_assumptions(syntax.ENot(e.cond)):
                else_branch = self.visit(e.else_branch)

            if cond == syntax.T:
                return then_branch
            if cond == syntax.F:
                return else_branch

            return syntax.ECond(cond, then_branch, else_branch).with_type(e.type)

        def visit_EFlatMap(self, e):
            bag = self.visit(e.e)
            with extend_assumptions(syntax.EIn(e.f.arg, bag)):
                f_body = self.visit(e.f.body)
            if isinstance(bag, syntax.EEmptyList) or isinstance(f_body, syntax.EEmptyList):
                return syntax.EEmptyList().with_type(e.type)
            if isinstance(bag, syntax.ESingleton):
                apply(syntax.ELambda(e.f.arg, f_body), bag.e)

            # lb1, ub1 = size_analysis(bag)
            # lb2, ub2 = size_analysis(f_body)
            # if ub1 < INFINITY and ub2 < INFINITY:
            #     print("---")
            #     print("|e| in [{}, {}]".format(lb1, ub1))
            #     print("|f| in [{}, {}]".format(lb2, ub2))
            #     print(pprint(bag))
            #     print(pprint(f_body))
            #     raise NotImplementedError()

            return target_syntax.EFlatMap(bag, syntax.ELambda(e.f.arg, f_body)).with_type(e.type)

        def visit_EFilter(self, e):
            bag = self.visit(e.e)
            with extend_assumptions(syntax.EIn(e.p.arg, bag)):
                f_body = self.visit(e.p.body)
            if isinstance(bag, syntax.EEmptyList):
                return syntax.EEmptyList().with_type(e.type)

            # lb, ub = size_analysis(bag)
            # if ub < INFINITY:
            #     print("---")
            #     print("|e| in [{}, {}]".format(lb, ub))
            #     print(pprint(bag))
            #     raise NotImplementedError()

            return target_syntax.EFilter(bag, syntax.ELambda(e.p.arg, f_body)).with_type(e.type)

        def visit_EMap(self, e):
            bag = self.visit(e.e)
            with extend_assumptions(syntax.EIn(e.f.arg, bag)):
                f_body = self.visit(e.f.body)
            if f_body == e.f.arg:
                return bag
            if isinstance(bag, syntax.EEmptyList):
                return syntax.EEmptyList().with_type(e.type)

            # lb, ub = size_analysis(bag)
            # if ub < INFINITY:
            #     print("---")
            #     print("|e| in [{}, {}]".format(lb, ub))
            #     print(pprint(bag))
            #     raise NotImplementedError()

            return target_syntax.EMap(bag, syntax.ELambda(e.f.arg, f_body)).with_type(e.type)

        def visit(self, e):
            if isinstance(e, syntax.Exp) and not isinstance(e, syntax.ELambda):
                if e.type == syntax.BOOL:
                    if any(alpha_equivalent(a, nnf(e)) for a in assumptions):
                        return syntax.T
                    if any(alpha_equivalent(a, nnf(syntax.ENot(e))) for a in assumptions):
                        return syntax.F
            e = super().visit(e)
            if isinstance(e, syntax.Exp) and not isinstance(e, syntax.ELambda):
                if not free_vars(e) and not free_funcs(e):
                    e = uneval(e.type, eval(e, {}))
            return e

    return V().visit(e)

# def checked_bag_delta(e, context, s, assumptions : syntax.Exp = syntax.T):
#     tup = bag_delta(e, context, s, assumptions)
#     # added, removed = tup
#     # if not definitely(singleton_or_empty(added)):
#     #     raise ValueError()
#     # if not definitely(singleton_or_empty(removed)):
#     #     raise ValueError()
#     # if not isinstance(added, syntax.EEmptyList) and alpha_equivalent(added, removed):
#     #     empty = syntax.EEmptyList().with_type(tup[0].type)
#     #     return (empty, empty)
#     return (added, removed)
#     from cozy.contexts import RootCtx
#     n, d = tup
#     new_e = mutate(e, s)
#     try:
#         assert_eq(as_bag(syntax.EBinOp(new_e, "-", e).with_type(e.type)), as_bag(n), context=RootCtx((), ()))
#         assert_eq(as_bag(syntax.EBinOp(e, "-", new_e).with_type(e.type)), as_bag(d), context=RootCtx((), ()))
#     except:
#         print("=" * 20)
#         print("exp: {}".format(pprint(e)))
#         print("stm:")
#         print(pprint(s))
#         raise
#     return tup

class MaybeType(object):
    def __bool__(self):
        raise ValueError("attempt to convert Maybe to a bool")
    def __str__(self):
        return "Maybe"
    def __repr__(self):
        return type(self).__name__ + "()"

MAYBE = MaybeType()

def definitely(v):
    if isinstance(v, MaybeType):
        return False
    return bool(v)

def possibly(v):
    if isinstance(v, MaybeType):
        return True
    return bool(v)

def both(x, y):
    if definitely(x) and definitely(y):
        return True
    if possibly(x) and possibly(y):
        return MAYBE
    return False

def either(x, y):
    if definitely(x) or definitely(y):
        return True
    if possibly(x) or possibly(y):
        return MAYBE
    return False

def invert(x):
    if definitely(x):
        return False
    if not possibly(x):
        return True
    return MAYBE

def singleton_or_empty(e):
    _, ub = size_analysis(e)
    if ub <= 1:
        return True
    return MAYBE
    # if isinstance(e, syntax.EEmptyList) or isinstance(e, syntax.ESingleton):
    #     return True
    # if isinstance(e, target_syntax.EStateVar):
    #     return singleton_or_empty(e.e)
    # if isinstance(e, target_syntax.EMap):
    #     return singleton_or_empty(e.e)
    # if isinstance(e, target_syntax.EFilter):
    #     return singleton_or_empty(e.e)
    # if isinstance(e, target_syntax.EFlatMap):
    #     return both(singleton_or_empty(e.e), singleton_or_empty(e.f.body))
    # if isinstance(e, syntax.EUnaryOp) and e.op == syntax.UOp.Distinct:
    #     return singleton_or_empty(e.e)
    # if isinstance(e, syntax.ECond):
    #     then_case = singleton_or_empty(e.then_branch)
    #     else_case = singleton_or_empty(e.else_branch)
    #     if definitely(then_case) and definitely(else_case):
    #         return True
    #     if possibly(then_case) or possibly(else_case):
    #         return MAYBE
    #     return False
    # if isinstance(e, syntax.EBinOp):
    #     if e.op == "intersect":
    #         return either(singleton_or_empty(e.e1), singleton_or_empty(e.e2))
    # return MAYBE

def is_singleton(e):
    lb, ub = size_analysis(e)
    if lb == 1 and ub == 1:
        return True
    return MAYBE
    # if isinstance(e, syntax.ESingleton):
    #     return True
    # if isinstance(e, target_syntax.EMap):
    #     return is_singleton(e.e)
    # if isinstance(e, syntax.EUnaryOp) and e.op == syntax.UOp.Distinct:
    #     return is_singleton(e.e)
    # return MAYBE

def is_empty(e):
    _, ub = size_analysis(e)
    if ub == 0:
        return True
    return MAYBE
    # if isinstance(e, syntax.EEmptyList):
    #     return True
    # if isinstance(e, target_syntax.EMap):
    #     return is_empty(e.e)
    # if isinstance(e, target_syntax.EFilter):
    #     return is_empty(e.e)
    # if isinstance(e, syntax.EUnaryOp) and e.op == syntax.UOp.Distinct:
    #     return is_empty(e.e)
    # return MAYBE

def edistinct(e):
    if definitely(singleton_or_empty(e)):
        return e
    return syntax.EUnaryOp(syntax.UOp.Distinct, e).with_type(e.type)

def equal(e1, e2):
    if isinstance(e1, syntax.EMakeRecord) and isinstance(e2, syntax.EMakeRecord):
        return syntax.EAll([
            simplify(equal(dict(e1.fields)[f], dict(e2.fields)[f]))
            for f, ft in e1.type])
    return syntax.EEq(e1, e2)

def not_equal(e1, e2):
    return syntax.ENe(e1, e2)

def exists(e):
    assert is_collection(e.type)
    if isinstance(e, target_syntax.EMap):
        return exists(e.e)
    if definitely(is_empty(e)):
        return syntax.F
    if definitely(is_singleton(e)):
        return syntax.T
    if isinstance(e, syntax.EBinOp) and e.op == "+":
        return syntax.EAny([
            exists(e.e1),
            exists(e.e2)])
    if isinstance(e, syntax.ECond):
        return cond(e.cond,
            exists(e.then_branch),
            exists(e.else_branch))
    return syntax.EExists(e)

def len_of(e):
    if definitely(singleton_or_empty(e)):
        return cond(exists(e), syntax.ONE, syntax.ZERO)
    if isinstance(e, target_syntax.EMap):
        return len_of(e.e)
    if isinstance(e, syntax.ECond):
        return cond(e.cond,
            len_of(e.then_branch),
            len_of(e.else_branch))
    return syntax.ELen(e)

def is_zero(e):
    if isinstance(e, syntax.ECond):
        return cond(e.cond, is_zero(e.then_branch), is_zero(e.else_branch))
    return syntax.EEq(e, syntax.ZERO)

from cozy.syntax_tools import nnf

def changed(e, context, s):
    if alpha_equivalent(e, mutate(e, s)):
        return syntax.F

    if isinstance(e, syntax.EUnaryOp):
        if e.op == syntax.UOp.Not:
            return changed(e.e, context, s)
        # if e.op == syntax.UOp.Exists:
        #     n, d = bag_delta(e.e, s)
        #     return cond(e,
        #         is_zero(len_of(e.e) - len_of(d) + len_of(n)),
        #         syntax.EUnaryOp(syntax.UOp.Exists, n))

    if isinstance(e, syntax.ESingleton):
        return changed(e.e, context, s)

    # if isinstance(e, syntax.EBinOp):
    #     if e.op == syntax.BOp.Or:
    #         return changed(syntax.ECond(e.e1, syntax.T, e.e2).with_type(syntax.BOOL), context, s)
    #     if e.op == syntax.BOp.And:
    #         return changed(syntax.ECond(e.e1, e.e2, syntax.F).with_type(syntax.BOOL), context, s)

    # if isinstance(e, syntax.ECond):
    #     return cond(changed(e.cond, context, s),
    #         cond(e.cond,
    #             not_equal(e.then_branch, mutate(e.else_branch, s)),  # transition T -> F
    #             not_equal(e.else_branch, mutate(e.then_branch, s))), # transition F -> T
    #         cond(e.cond,
    #             changed(e.then_branch, context, s),
    #             changed(e.else_branch, context, s)))

    return syntax.ENe(e, better_mutate(target_syntax.EStateVar(e).with_type(e.type), context, s))
    raise NotImplementedError(pprint(e))

def element_of(x, xs):
    if isinstance(xs, target_syntax.EFilter):
        return element_of(x, xs.e)
    if isinstance(xs, syntax.EEmptyList):
        return False
    if isinstance(x, syntax.EUnaryOp) and x.op == syntax.UOp.The:
        return both(subset_of(x.e, xs), invert(is_empty(x.e)))
    return MAYBE

def subset_of(xs, ys):
    if alpha_equivalent(xs, ys):
        return True
    if isinstance(xs, syntax.EEmptyList):
        return True
    if isinstance(xs, syntax.ECond):
        s1 = subset_of(xs.then_branch, ys)
        s2 = subset_of(xs.else_branch, ys)
        if definitely(s1) and definitely(s2):
            return True
        if possibly(s1) and possibly(s2):
            return MAYBE
        return False
    if isinstance(xs, target_syntax.ESingleton):
        return element_of(xs.e, ys)
    if isinstance(xs, target_syntax.EFilter):
        return subset_of(xs.e, ys)
    if isinstance(xs, target_syntax.EMap) and xs.f.arg == xs.f.body:
        return subset_of(xs.e, ys)
    if isinstance(ys, target_syntax.EMap) and ys.f.arg == ys.f.body:
        return subset_of(xs, ys.e)
    return MAYBE

def to_bag(e):
    x = syntax.EVar("x").with_type(e.type.t)
    return target_syntax.EMap(e, syntax.ELambda(x, x)).with_type(syntax.TBag(e.type.t))

def types_equiv(t1, t2):
    if is_collection(t1) and is_collection(t2):
        return types_equiv(t1.t, t2.t)
    return t1 == t2

def dbg(f):

    @functools.wraps(f)
    def dbg_wrapper(e, context, s, assumptions : syntax.Exp = syntax.T):

        # assert exp_wf(e, context, STATE_POOL), "input not wf: {} in {}".format(pprint(e), context)

        assert context.legal_for(free_vars(e))
        res = f(e, context, s, assumptions)
        n, d = res
        # from cozy.syntax_tools import deep_copy
        # dc = deep_copy(n)
        # assert retypecheck(dc), pprint(n)
        # assert types_equiv(dc.type, n.type), "{} vs {}".format(pprint(n.type), pprint(dc.type))
        assert types_equiv(n.type, e.type), "{} + {}".format(pprint(e), pprint(n))
        assert types_equiv(d.type, e.type), "{} - {}".format(pprint(e), pprint(d))
        n = partial_eval(n)
        d = partial_eval(d)
        assert types_equiv(n.type, e.type), "{} + {}".format(pprint(e), pprint(n))
        assert types_equiv(d.type, e.type), "{} - {}".format(pprint(e), pprint(d))

        # assert exp_wf(n, context, RUNTIME_POOL), "output [added] not wf: {} ----> {} in {}".format(pprint(e), pprint(n), context)
        # assert exp_wf(d, context, RUNTIME_POOL), "output [removed] not wf: {} ----> {} in {}".format(pprint(e), pprint(d), context)

        interp = e - d + n
        print("delta {}: +{}, -{}".format(
            pprint(e), pprint(n), pprint(d)))
        # # print("delta {}: {}".format(pprint(e), pprint(interp)))
        # interp = partial_eval(interp)
        # # print("delta {}: {}".format(pprint(e), pprint(interp)))
        # interp = cse(interp)
        # print("delta {}: {}".format(pprint(e), pprint(interp)))

        # assert definitely(singleton_or_empty(d))
        # assert definitely(singleton_or_empty(n))
        assert context.legal_for(free_vars(n)), free_vars(n)
        assert context.legal_for(free_vars(d)), free_vars(d)

        if alpha_equivalent(n, d):
            n = d = syntax.EEmptyList().with_type(e.type)

        # lb1, ub1 = size_analysis(n)
        # lb2, ub2 = size_analysis(d)
        # if not (ub1 < INFINITY and ub2 < INFINITY):
        #     print("|n| in [{}, {}]".format(lb1, ub1))
        #     print("|d| in [{}, {}]".format(lb2, ub2))
        #     raise NotEfficient(e)

        assumptions_to_use = syntax.T

        # check_valid(context, syntax.EImplies(assumptions_to_use, syntax.EIsSubset(d, e)),
        #     debug={
        #         "bag": e,
        #         "deleted": d,
        #         "true deleted": e - mutate(e, s)})
        # check_valid(context, syntax.EImplies(assumptions_to_use, target_syntax.EDisjoint(n, d)),
        #     debug={
        #         "bag": e,
        #         "deleted": d,
        #         "true deleted": e - mutate(e, s),
        #         "added": n,
        #         "true added": mutate(e, s) - e})
        # check_valid(context, syntax.EImplies(
        #     assumptions_to_use,
        #     syntax.ELe(syntax.ELen(d), syntax.ONE)),
        #     debug={
        #     "bag": e,
        #     "bag_prime": mutate(e, s),
        #     "removed": d,
        #     "added": n,
        #     })

        if False:
            print("checking delta valid...")
            e_prime = mutate(e, s)
            check_valid(context, syntax.EImplies(
                assumptions_to_use,
                syntax.EEq(to_bag(e_prime), to_bag(interp))),
                debug={
                    "e": e,
                    "e'": e_prime,
                    "d": d,
                    "n": n,
                    "e - d + n": interp,
                })
            print("done!")

        return res
    return dbg_wrapper

def became_true(e, context, s, assumptions):
    return became_bool(e, context, s, True, assumptions)

def became_false(e, context, s, assumptions):
    return became_bool(e, context, s, False, assumptions)

def check_valid(context, formula, debug={}):
    model = minimal_model(syntax.ENot(formula), solver=solver_for(context))
    if model is not None:
        print("{} is not valid".format(pprint(formula)))
        print("in model {}".format(model))
        for thing, exp in debug.items():
            print(" - {} = {}".format(thing, pprint(exp)))
            print(" - {} evals to {}".format(thing, eval(exp, model)))
        raise AssertionError()

def checked_become_bool(f):
    def g(e, context, s, val, assumptions):
        res = f(e, context, s, val, assumptions)
        # check_valid(context, syntax.EImplies(assumptions,
        #     syntax.EImplies(syntax.EEq(e, syntax.EBool(not val).with_type(syntax.BOOL)),
        #         syntax.EEq(
        #             res,
        #             syntax.EEq(mutate(e, s), syntax.EBool(val).with_type(syntax.BOOL))))))
        return res
    return g

def nonnegative(x):
    if isinstance(x, syntax.EUnaryOp) and x.op == syntax.UOp.Length:
        return True
    if isinstance(x, syntax.EBinOp) and x.op == "+":
        return both(nonnegative(x.e1), nonnegative(x.e2))
    return MAYBE

def ge(x, y):
    if isinstance(x, syntax.ECond):
        return cond(x.cond,
            ge(x.then_branch, y),
            ge(x.else_branch, y))
    if isinstance(y, syntax.ECond):
        return cond(y.cond,
            ge(x, y.then_branch),
            ge(x, y.else_branch))
    if definitely(nonnegative(x)) and y == syntax.ZERO:
        return syntax.T
    if x == syntax.ZERO and isinstance(y, syntax.EUnaryOp) and y.op == syntax.UOp.Length:
        return syntax.ENot(exists(y.e))
    return syntax.EGe(x, y)

@checked_become_bool
def became_bool(e, context, s, val, assumptions):
    """
    Assuming that boolean expression `e` evaluates to (not val),
    does it evaluate to (val) after executing s?
    """
    if alpha_equivalent(e, mutate(e, s)):
        return syntax.F

    if isinstance(e, syntax.EUnaryOp):
        if e.op == syntax.UOp.Not:
            return became_bool(e.e, context, s, not val, assumptions)
        if e.op == syntax.UOp.Exists:
            added, removed = bag_delta(e.e, context, s, assumptions)
            if val:
                return exists(added)
            else:
                return ge(
                    len_of(removed),
                    syntax.ESum([len_of(added), len_of(e.e)]))
    if isinstance(e, syntax.EBinOp):
        if e.op == syntax.BOp.And:
            if val:
                raise NotImplementedError(pprint(e))
                return syntax.EAll([
                    became_bool(e.e1, context, s, val, assumptions),
                    became_bool(e.e2, context, s, val, assumptions)])
            else:
                return syntax.EAny([
                    became_bool(e.e1, context, s, val, assumptions),
                    became_bool(e.e2, context, s, val, assumptions)])
        if e.op == syntax.BOp.Or:
            if val:
                return syntax.EAny([
                    became_bool(e.e1, context, s, val, assumptions),
                    became_bool(e.e2, context, s, val, assumptions)])
            else:
                # one (both?) of these are true...
                return cond(e.e1,
                    cond(e.e2,
                        syntax.EAll([
                            became_bool(e.e1, context, s, val, assumptions),
                            became_bool(e.e2, context, s, val, assumptions)]),
                        became_bool(e.e1, context, s, val, assumptions)),
                    became_bool(e.e2, context, s, val, assumptions))
    raise NotImplementedError(pprint(e))

def implies(e1, e2):
    if e1 == syntax.T:
        return e2
    if e1 == syntax.F:
        return syntax.T
    if e2 == syntax.T:
        return syntax.T
    if e2 == syntax.F:
        return syntax.ENot(e1)
    return syntax.EImplies(e1, e2)

# def infer_partition(e):
#     if isinstance(e, syntax.EUnaryOp):
#         return infer_partition(e.e)
#     if isinstance(e, syntax.ESingleton):
#         return infer_partition(e.e)
#     if isinstance(e, syntax.EGetField):
#         return infer_partition(e.e)
#     if isinstance(e, target_syntax.EFilter):
#         for cond in break_conj(nnf(e.p.body)):
#             if isinstance(cond, syntax.EBinOp) and cond.op in ("==", "==="):
#                 for x, y in [(cond.e1, cond.e2), (cond.e2, cond.e1)]:
#                     if e.p.arg in free_vars(x) and e.p.arg not in free_vars(y):
#                         return target_syntax.EMap(e.e, syntax.ELambda(e.p.arg, x)).with_type(syntax.TBag(x.type))
#     # if all(isinstance(c, syntax.Exp) for c in e.children()):
#     #     ps = [infer_partition(c) for c in e.children()]
#     raise NotEfficient(e)
#     # return None


# def find_changed_subset(e, context, s, var, bag):
#     """
#     Find the subset of `bag` such that e only changes due to s when var belongs
#     to that subset.
#     """
#     if alpha_equivalent(e, mutate(e, s)):
#         return syntax.EEmptyList().with_type(bag.type)

#     if not any(isinstance(c, syntax.ELambda) for c in e.children()):
#         return syntax.EUnion([find_changed_subset(c, context, s, var, bag) for c in e.children() if isinstance(c, syntax.Exp)], elem_type=var.type)

#     if isinstance(e, target_syntax.EMap) and alpha_equivalent(e.f, mutate(e.f, s)):
#         return find_changed_subset(e.e, context, s, var, bag)

#     if isinstance(e, target_syntax.EFilter) and alpha_equivalent(e.p, mutate(e.p, s)):
#         print(pprint(e))
#         raise NotImplementedError()

#     raise NotImplementedError(e)

class NotPossible(Exception):
    pass

# @typechecked
# def infer_partition(f : syntax.ELambda) -> (syntax.Exp, syntax.ELambda, syntax.ELambda, syntax.ELambda):
#     e = f.body
#     if isinstance(e, syntax.EUnaryOp):
#         domain, proj, g, res = infer_partition(syntax.ELambda(f.arg, e.e))
#         res = syntax.ELambda(res.arg, syntax.EUnaryOp(e.op, res.body).with_type(e.type))
#         return (domain, proj, g, res)
#     if isinstance(e, syntax.ESingleton):
#         domain, proj, g, res = infer_partition(syntax.ELambda(f.arg, e.e))
#         res = syntax.ELambda(res.arg, syntax.ESingleton(res.body).with_type(e.type))
#         return (domain, proj, g, res)
#     if isinstance(e, syntax.EGetField):
#         domain, proj, g, res = infer_partition(syntax.ELambda(f.arg, e.e))
#         res = syntax.ELambda(res.arg, syntax.EGetField(res.body, e.f).with_type(e.type))
#         return (domain, proj, g, res)
#     # if isinstance(e, syntax.EBinOp) or isinstance(e, syntax.ECond):
#     #     reses = [infer_partition(syntax.ELambda(f.arg, x)) for x in e.children() if isinstance(x, syntax.Exp)]
#     #     domains, projs, gs, ress = zip(*reses)
#     #     raise NotImplementedError(domains)
#     if isinstance(e, target_syntax.EFilter):
#         if f.arg not in free_vars(e.e):
#             for cond in break_conj(nnf(e.p.body)):
#                 if isinstance(cond, syntax.EBinOp) and cond.op in ("==", "==="):
#                     for x, y in [(cond.e1, cond.e2), (cond.e2, cond.e1)]:
#                         if e.p.arg in free_vars(x) and e.p.arg not in free_vars(y):
#                             domain = e.e
#                             proj = syntax.ELambda(e.p.arg, x)
#                             g = syntax.ELambda(e.p.arg, y)
#                             res = mk_lambda(e.type, lambda x: x)
#                             return (domain, proj, g, res)
#     if isinstance(e, syntax.EArgMin) or isinstance(e, syntax.EArgMax) or isinstance(e, target_syntax.EMap) or isinstance(e, target_syntax.EFlatMap):
#         if f.arg not in free_vars(e.f):
#             domain, proj, g, res = infer_partition(syntax.ELambda(f.arg, e.e))
#             res = syntax.ELambda(res.arg, type(e)(res.body, e.f).with_type(e.type))
#             return (domain, proj, g, res)

#     raise NotPossible(pprint(e))


@functools.lru_cache()
@dbg
def bag_delta(e, context, s, assumptions : syntax.Exp = syntax.T):
    # print("-" * 20)
    # print("{}.....{}".format(pprint(e), pprint(s)))

    empty = syntax.EEmptyList().with_type(e.type)
    new_e = mutate(e, s)

    if alpha_equivalent(e, new_e):
        return (empty, empty)

    # return (new_e - e, e - new_e)

    if isinstance(e, target_syntax.EStateVar):
        raise ValueError(e)
        # return bag_delta(e.e, context, s, assumptions)

    if isinstance(e, target_syntax.EMap):
        t = e.type
        e = target_syntax.EFlatMap(e.e, syntax.ELambda(e.f.arg,
            syntax.ESingleton(e.f.body).with_type(t))).with_type(t)

    if isinstance(e, target_syntax.EFilter):
        t = e.type
        e = target_syntax.EFlatMap(e.e, syntax.ELambda(e.p.arg,
            cond(e.p.body,
                syntax.ESingleton(e.p.arg).with_type(t),
                syntax.EEmptyList().with_type(t)))).with_type(t)

    if isinstance(e, target_syntax.EFlatMap):
        arg = fresh_var(e.f.arg.type)
        func_body = apply(e.f, arg)

        xs = e.e
        added_xs, removed_xs = bag_delta(xs, context, s, assumptions)
        inner_context = UnderBinder(context, arg, xs, STATE_POOL)
        added_ys, removed_ys = bag_delta(func_body, inner_context, s, assumptions)

        # print("*** {}".format(pprint(e)))
        # print("D_{{xs}} = {}".format(pprint(removed_xs)))
        # print("A_{{xs}} = {}".format(pprint(added_xs)))
        # print("D_{{f}}  = {}".format(pprint(removed_ys)))
        # print("A_{{f}}  = {}".format(pprint(added_ys)))
        # if not (definitely(is_empty(added_ys)) and definitely(is_empty(removed_ys))):
        #     changed_subset = find_changed_subset(func_body, inner_context, s, arg, xs)
        #     print(" ---> {} changes only for {}".format(pprint(func_body), pprint(changed_subset)))
        #     domain = infer_partition(func_body)
        #     print(" ---> {} paritions {}".format(pprint(func_body), pprint(domain)))

        new_body = strip_EStateVar(better_mutate(statevar(func_body), inner_context, s, assumptions))
        # new_body = mutate(func_body, s)

        post_remove = bag_subtract(xs, removed_xs)

        if not definitely(singleton_or_empty(post_remove)):
            f = syntax.ELambda(arg, func_body)
            print("-" * 20)
            print("need to infer changes for {}".format(pprint(f)))
            print("post_remove: {}".format(pprint(post_remove)))
            changes = analyze_changes(f, context, s, assumptions)
            print("changes: {}".format(pprint(changes)))
            orig_post_remove = post_remove
            post_remove = bag_set_intersection(post_remove, changes)
            print("post_remove': {}".format(pprint(post_remove)))
            print("-" * 20)

            assert context.legal_for(free_vars(changes))

            # lb, ub = size_analysis(post_remove)
            # if ub == INFINITY:
            #     lb, ub = size_analysis(post_remove)
            #     print("size in [{}, {}]".format(lb, ub))
            #     print("unique? {}".format(are_unique(orig_post_remove)))
            #     raise NotEfficient(e)

            # raise NotImplementedError()

            # try:
            #     f = syntax.ELambda(arg, func_body)
            #     print("need to infer partition for {}".format(pprint(f)))
            #     domain, proj, g, res = infer_partition(f)
            #     print(pprint(domain))
            #     print(pprint(proj))
            #     print(pprint(g))
            #     print(pprint(res))
            #     print("--")
            #     domain_n, domain_d = bag_delta(emap(domain, proj), context, s, assumptions)
            #     possible_changes = bag_union(domain_n, domain_d)
            #     print(pprint(possible_changes))

            #     f_prime = syntax.ELambda(arg, mutate(func_body, s))
            #     check_valid(context, target_syntax.EForall(post_remove,
            #         lambda x: syntax.EImplies(
            #             syntax.ENot(syntax.EIn(x, possible_changes)),
            #             syntax.EEq(f.apply_to(x), f_prime.apply_to(x)))))

            #     print("the partition is valid!")
            #     post_remove = bag_intersection(possible_changes, post_remove)
            #     # print("For what values {} in {} is".format(arg.id, pprint(post_remove)))
            #     # print(" - " + pprint(removed_ys))
            #     # print(" + " + pprint(added_ys))
            #     # print("not empty?")
            #     # raise NotImplementedError()
            # except NotPossible:
            #     if not definitely(is_empty(added_ys)) or not definitely(is_empty(removed_ys)):
            #         print("warning: unable to infer partition for {}".format(pprint(f)))
            #         print(repr(f))
            #         print(repr(post_remove))

        removed = bag_union(
            flatmap(bag_intersection(xs, removed_xs), e.f),
            flatmap(post_remove, syntax.ELambda(arg, removed_ys)))
        added = bag_union(
            flatmap(added_xs, syntax.ELambda(arg, new_body)),
            flatmap(post_remove, syntax.ELambda(arg, added_ys)))

        # e_prime = mutate(e, s)
        # interp = e - removed + added
        # check_valid(context, syntax.EEq(to_bag(e_prime), to_bag(interp)),
        #     debug={
        #         "e": e,
        #         "e'": e_prime,
        #         "d": removed,
        #         "n": added,
        #         "d[xs]": removed_xs,
        #         "n[xs]": added_xs,
        #         "e - d + n": interp,
        #     })

        # if alpha_equivalent(added, removed):
        #     return (empty, empty)
        return (added, removed)

    if isinstance(e, syntax.EBinOp) and e.op == "+":
        n1, d1 = bag_delta(e.e1, context, s, assumptions)
        n2, d2 = bag_delta(e.e2, context, s, assumptions)
        return (bag_union(n1, n2), bag_union(d1, d2))

    if isinstance(e, syntax.EBinOp) and e.op == "-":
        # (xs - d1 + n1) - (ys - d2 + n2)
        # assume ys' \subsetof xs
        # assume ys \subsetof xs
        n1, d1 = bag_delta(e.e1, context, s, assumptions)
        n2, d2 = bag_delta(e.e2, context, s, assumptions)
        return (
            bag_union(n1, d2),
            bag_union(d1, n2))

    if isinstance(e, syntax.EUnaryOp) and e.op == syntax.UOp.Distinct:
        n, d = bag_delta(e.e, context, s, assumptions)
        print("{} : {}".format(pprint(e.e), pprint(e.e.type)))
        print("{} : {}".format(pprint(d), pprint(d.type)))
        if not definitely(are_unique(e.e)):
            x = fresh_var(e.type.t)
            x = fresh_var(e.type.t)
            d = efilter(edistinct(d), syntax.ELambda(x, equal(countin(x, e.e), syntax.ONE)))
            print("{} : {}".format(pprint(d), pprint(d.type)))
            n = efilter(edistinct(n), syntax.ELambda(x, equal(countin(x, bag_subtract(e.e, d)), syntax.ZERO)))
        return (n, d)

    if isinstance(e, syntax.ESingleton):
        # new_e = mutate(e.e, s)
        new_e = strip_EStateVar(better_mutate(statevar(e.e), context, s, assumptions))
        if alpha_equivalent(new_e, e.e):
            return (empty, empty)
        else:
            # ch = changed(e, context, s)
            # return (
            #     cond(ch, syntax.ESingleton(new_e).with_type(e.type), empty),
            #     cond(ch, e, empty))
            return (syntax.ESingleton(new_e).with_type(e.type), e)

    if isinstance(e, syntax.EEmptyList):
        return (empty, empty)

    if isinstance(e, syntax.ECond):
        # new_cond = mutate(e.cond, s)
        new_cond = strip_EStateVar(better_mutate(statevar(e.cond), context, s, assumptions))
        if alpha_equivalent(new_cond, e.cond):
            n1, d1 = bag_delta(e.then_branch, context, s, assumptions)
            n2, d2 = bag_delta(e.else_branch, context, s, assumptions)
            return (
                cond(e.cond, n1, n2),
                cond(e.cond, d1, d2))
        else:
            # print(" -> {}".format(pprint(e.cond)))
            # print(" becomes T: {}".format(pprint(became_true (e.cond, context, s, assumptions))))
            # print(" becomes F: {}".format(pprint(became_false(e.cond, context, s, assumptions))))

            case1 = cond(became_false(e.cond, context, s, assumptions), bag_subtract(e.else_branch, e.then_branch), empty)
            case2 = cond(became_true (e.cond, context, s, assumptions), bag_subtract(e.then_branch, e.else_branch), empty)
            case3 = cond(became_false(e.cond, context, s, assumptions), bag_subtract(e.then_branch, e.else_branch), empty)
            case4 = cond(became_true (e.cond, context, s, assumptions), bag_subtract(e.else_branch, e.then_branch), empty)
            added = cond(e.cond, case1, case2)
            removed = cond(e.cond, case3, case4)
            return (added, removed)

    # if isinstance(e, syntax.EVar):
    #     n = d = syntax.EEmptyList().with_type(e.type)
    #     for step in flatten(s):
    #         if isinstance(step, syntax.SCall):
    #             assert isinstance(step.target, syntax.EVar)
    #             if step.target == e:
    #                 if step.func == "add_all":
    #                     n = bag_union(n, step.args[0])
    #                 elif step.func == "remove_all":
    #                     d = bag_union(d, step.args[0])
    #                 else:
    #                     raise ValueError(step.func)
    #         elif isinstance(step, syntax.SAssign) and isinstance(step.lhs, syntax.EVar) and step.lhs != e:
    #             pass
    #         else:
    #             raise NotImplementedError(step)
    #     from cozy.typecheck import retypecheck, is_collection
    #     assert retypecheck(n)
    #     assert retypecheck(d)
    #     assert is_collection(n.type), pprint(n)
    #     assert is_collection(d.type), pprint(d)
    #     return (n, d)

    # raise NotImplementedError(type(e))

    # if isinstance(e, syntax.ELet):
    #     if alpha_equivalent(e.e, mutate(e.e, s)):
    #         ctx = UnderBinder(context, e.f.arg, syntax.ESingleton(e.e).with_type(syntax.TBag(e.e.type)), RUNTIME_POOL)
    #         n, d = bag_delta(e.f.body, ctx, s, assumptions)
    #         return (
    #             syntax.ELet(e.e, syntax.ELambda(e.f.arg, n)),
    #             syntax.ELet(e.e, syntax.ELambda(e.f.arg, d)))

    if not isinstance(e, syntax.EVar):
        raise NotImplementedError(pprint(e))

    @typechecked
    def infer_delta(old : syntax.EVar, new : syntax.Exp) -> (syntax.Exp, syntax.Exp):
        if new == old:
            return (empty, empty)
        if isinstance(new, syntax.ELet):
            assert old != new.f.arg
            n, d = infer_delta(old, new.f.body)
            return (
                qsubst(n, new.f.arg, new.e),
                qsubst(d, new.f.arg, new.e))
        if isinstance(new, syntax.EBinOp) and new.op == "+":
            n, d = infer_delta(old, new.e1)
            return (bag_union(n, new.e2), d)
        if isinstance(new, syntax.EBinOp) and new.op == "-" and new.e1 == old:
            return (empty, bag_intersection(old, new.e2))
        raise NotImplementedError("{} -----> {}".format(pprint(old), pprint(new)))

    return infer_delta(e, new_e)

    # new_e = repair_EStateVar_in_context(new_e, context)
    # print(new_e)

    # if isinstance(new_e, syntax.EBinOp) and new_e.op == "+" and isinstance(new_e.e1, syntax.EBinOp) and new_e.e1.op == "-" and alpha_equivalent(new_e.e1.e1, e):
    #     return (new_e.e2, new_e.e1.e2)

    # raise NotImplementedError("{} -----> {}".format(pprint(e), pprint(new_e)))
    # return (
    #     bag_subtract(new_e, e),
    #     bag_subtract(e, new_e))

    # if isinstance(s, syntax.SCall) and s.target == e:
    #     if s.func == "add_all":
    #         return (s.args[0], empty)
    #     if s.func == "add":
    #         return (syntax.ESingleton(s.args[0]).with_type(e.type), empty)
    #     if s.func == "remove_all":
    #         return (empty, s.args[0])
    #     if s.func == "remove":
    #         return (empty, syntax.ESingleton(s.args[0]).with_type(e.type))
    #     return (empty, empty)

    # if isinstance(s, syntax.SCall) and isinstance(e, syntax.EVar):
    #     return (empty, empty)

    # if isinstance(s, syntax.SSeq):
    #     while isinstance(s.s1, syntax.SSeq):
    #         s = syntax.SSeq(s.s1.s1, syntax.SSeq(s.s1.s2, s.s2))
    #     if isinstance(s.s1, syntax.SDecl):
    #         n, d = bag_delta(e, s.s2)
    #         n = subst(n, { s.s1.id : s.s1.val })
    #         d = subst(d, { s.s1.id : s.s1.val })
    #         return (n, d)
    #     n1, d1 = bag_delta(e, s.s1)
    #     return bag_delta(bag_union(bag_subtract(e, d1), n1), s.s2)
    #     # n2, d2 = bag_delta(e, s.s2)
    #     # return (
    #     #     bag_union(n1, n2),
    #     #     bag_union(d1, d2))

    # if isinstance(s, syntax.SIf):
    #     nt, dt = bag_delta(e, s.then_branch)
    #     ne, de = bag_delta(e, s.else_branch)
    #     return (cond(s.cond, nt, ne), cond(s.cond, dt, de))

    # if alpha_equivalent(e, mutate(e, s)):
    #     return (empty, empty)

    # # if isinstance(s, syntax.SAssign):
    # #     if alpha_equivalent(e, mutate(e, s)):
    # #         return syntax.EEmptyList().with_type(e.type)

    # print(pprint(e))
    # print(pprint(s))
    # raise NotImplementedError()

# def new_elems(e, s):
#     return bag_delta(e, s)[1]

# def del_elems(e, s):
#     return bag_delta(e, s)[0]

# @typechecked
# def better_mutate_statevars(
#         e       : syntax.Exp,
#         context : Context,
#         op      : syntax.Stm) -> syntax.Exp:
#     class V(BottomUpRewriter):
#         def visit_EStateVar(self, e):
#             return better_mutate(e, context, op)
#     return V().visit(e)

def repair_EStateVar(e : syntax.Exp, available_state : [syntax.Exp]) -> syntax.Exp:
    class V(BottomUpRewriter):
        def visit_EStateVar(self, e):
            return e
        def visit_Exp(self, e):
            if any(alpha_equivalent(e, x) for x in available_state):
                return target_syntax.EStateVar(e).with_type(e.type)
            return super().visit_ADT(e)
    return V().visit(strip_EStateVar(e))

def repair_EStateVar_in_context(e : syntax.Exp, context : Context, available_state : [syntax.Exp] = []) -> syntax.Exp:
    with task("repairing statevars"):

        available_state = list(unique(itertools.chain(
            available_state,
            (v for v, p in context.vars() if p == STATE_POOL))))

        class V(BottomUpRewriter):
            def visit_EStateVar(self, e):
                wf = exp_wf(e.e, context, STATE_POOL)
                if wf:
                    return e
                # print("WARNING: {} not a well-formed concretization function (wf={})".format(pprint(e.e), wf))
                return self.visit(strip_EStateVar(e.e))
            def visit_Exp(self, e):
                if any(alpha_equivalent(e, x) for x in available_state):
                    return target_syntax.EStateVar(e).with_type(e.type)
                return super().visit_ADT(e)

        with task("visiting nodes", size=e.size()):
            e = V().visit(e)

        with task("freshening binders"):
            e = freshen_binders(e, context)

        with task("checking correctness"):
            assert context.legal_for(free_vars(e)), "ctx={}, fvs={}".format(context, free_vars(e))
            assert exp_wf(e, context, RUNTIME_POOL)

        return e

def replace_get_value(e : syntax.Exp, ptr : syntax.Exp, new_value : syntax.Exp) -> syntax.Exp:
    """
    Return an expression representing the value of `e` after writing
    `new_value` to `ptr`.

    This amounts to replacing all instances of `_.val` in `e` with

        (_ == ptr) ? (new_value) : (_.val)
    """
    t = ptr.type
    fvs = free_vars(ptr) | free_vars(new_value)
    class V(BottomUpRewriter):
        def visit_ELambda(self, e):
            if e.arg in fvs:
                v = fresh_var(e.arg.type, omit=fvs)
                e = syntax.ELambda(v, apply(e, v))
            return syntax.ELambda(e.arg, self.visit(e.body))
        def visit_EGetField(self, e):
            ee = self.visit(e.e)
            res = syntax.EGetField(ee, e.f).with_type(e.type)
            if e.e.type == t and e.f == "val":
                res = syntax.ECond(syntax.EEq(ee, ptr), new_value, res).with_type(e.type)
            return res
    return V().visit(e)

def _do_assignment(lval : syntax.Exp, new_value : syntax.Exp, e : syntax.Exp) -> syntax.Exp:
    """
    Return the value of `e` after the assignment `lval = new_value`.
    """
    if isinstance(lval, syntax.EVar):
        return qsubst(e, lval, new_value)
        # return subst(e, { lval.id : new_value })
    elif isinstance(lval, syntax.EGetField):
        if isinstance(lval.e.type, syntax.THandle):
            assert lval.f == "val"
            # Because any two handles might alias, we need to rewrite all
            # reachable handles in `e`.
            return replace_get_value(e, lval.e, new_value)
        return _do_assignment(lval.e, _replace_field(lval.e, lval.f, new_value), e)
    else:
        raise Exception("not an lvalue: {}".format(pprint(lval)))

def _replace_field(record : syntax.Exp, field : str, new_value : syntax.Exp) -> syntax.Exp:
    return syntax.EMakeRecord(tuple(
        (f, new_value if f == field else syntax.EGetField(record, f).with_type(ft))
        for f, ft in record.type.fields)).with_type(record.type)

def pprint_value(ty, val):
    if isinstance(ty, syntax.TBag) or isinstance(ty, syntax.TSet):
        if not val: return "{}"
        if len(val) == 1: return "{{{}}}".format(pprint_value(ty.t, val[0]))
        return "{{\n    {}}}".format(",\n    ".join(pprint_value(ty.t, v) for v in val))
    if isinstance(ty, syntax.TList):
        if not val: return "[]"
        if len(val) == 1: return "[{}]".format(pprint_value(ty.t, val[0]))
        return "[\n    {}]".format(",\n    ".join(pprint_value(ty.t, v) for v in val))
    if isinstance(ty, syntax.TRecord):
        return "{{{}}}".format(", ".join("{}: {}".format(f, val[f]) for f, ft in sorted(ty.fields)))
    if isinstance(ty, syntax.TNative):
        return "${}".format(val[1])
    if isinstance(ty, target_syntax.TMap):
        return "{{{}}}".format(", ".join("{} -> {}".format(*i) for i in val.items()))
    return repr(val)

def pprint_model(model, env):
    for var_id, val in sorted(model.items()):
        if var_id not in env:
            print("  {} = {!r}".format(var_id, val))
            continue
        ty = env[var_id]
        print("  {} = {}".format(var_id, pprint_value(ty, val)))

def minimal_model(formula, collection_depth=4, solver=None):
    if solver is None:
        from cozy.solver import IncrementalSolver
        solver = IncrementalSolver(collection_depth=collection_depth)
    if solver.satisfiable(formula):
        print("Minimizing model...")
        from cozy.typecheck import is_collection
        collections = [v for v in free_vars(formula) if is_collection(v.type)]
        for max_len in range(collection_depth * len(collections) + 1):
            model = solver.satisfy(syntax.EAll([
                syntax.ELt(syntax.ESum([syntax.ELen(v) for v in collections]), syntax.ENum(max_len).with_type(syntax.INT)),
                formula]))
            if model is not None:
                return model
    return None

# def mutate_in_place(
#         lval           : syntax.Exp,
#         e              : syntax.Exp,
#         op             : syntax.Stm,
#         abstract_state : [syntax.EVar],
#         assumptions    : [syntax.Exp] = None,
#         invariants     : [syntax.Exp] = None,
#         subgoals_out   : [syntax.Query] = None):

#     if False:
#         if assumptions is None:
#             assumptions = []

#         if subgoals_out is None:
#             subgoals_out = []

#         parts = []

#         for stm in flatten(op):
#             parts.extend(break_seq(_mutate_in_place(
#                 lval, e, stm, abstract_state, assumptions, invariants, subgoals_out)))

#         return syntax.seq(parts)

#     return _mutate_in_place(
#         lval, e, op, abstract_state, assumptions, invariants, subgoals_out)

def mutate_in_place(
        lval           : syntax.Exp,
        e              : syntax.Exp,
        op             : syntax.Stm,
        abstract_state : [syntax.EVar],
        assumptions    : [syntax.Exp] = None,
        invariants     : [syntax.Exp] = None,
        subgoals_out   : [syntax.Query] = None) -> syntax.Stm:
    """
    Produce code to update `lval` that tracks derived value `e` when `op` is
    run.
    """

    if assumptions is None:
        assumptions = []

    if invariants is None:
        invariants = []

    if subgoals_out is None:
        subgoals_out = []

    def make_subgoal(e, a=[], docstring=None):
        if skip_stateless_synthesis.value and not any(v in abstract_state for v in free_vars(e)):
            return e
        query_name = fresh_name("query")
        query = syntax.Query(query_name, syntax.Visibility.Internal, [], assumptions + a, e, docstring)
        query_vars = [v for v in free_vars(query) if v not in abstract_state]
        query.args = [(arg.id, arg.type) for arg in query_vars]
        subgoals_out.append(query)
        return syntax.ECall(query_name, tuple(query_vars)).with_type(e.type)

    h = extension_handler(type(lval.type))
    if h is not None:
        return h.mutate_in_place(
            lval=lval,
            e=e,
            op=op,
            assumptions=assumptions,
            invariants=invariants,
            make_subgoal=make_subgoal)

    # fallback: use an update sketch
    new_e = mutate(e, op)

    if False:
        vars = free_vars(e) | free_vars(op)
        from cozy.contexts import RootCtx
        from cozy.common import partition
        state_vars, args = partition(vars, lambda v: v in abstract_state)
        context = RootCtx(state_vars=state_vars, args=args)
        new_e_prime = better_mutate(target_syntax.EStateVar(e).with_type(e.type), context, op, assumptions=syntax.EAll(assumptions))
        model = minimal_model(syntax.EAll(assumptions + [syntax.ENot(syntax.EEq(new_e, new_e_prime))]))
        if model is not None:
            from cozy.evaluation import eval
            from cozy.contexts import shred
            from cozy.common import unique

            print(pprint(op))
            pprint_model(model, { v.id : v.type for v in (free_vars(e) | free_vars(syntax.EAll(assumptions))) })
            print("--->")
            for v in (free_vars(e) | free_vars(syntax.EAll(assumptions))):
                print("  {} = {}".format(v.id, pprint_value(v.type, eval(mutate(v, op), model))))

            print(pprint(new_e))
            print(pprint(new_e_prime))

            print("expected: {}".format(eval(new_e, model)))
            print("got: {}".format(eval(new_e_prime, model)))

            for x, x_ctx, _ in unique(shred(new_e_prime, context)):
                if x_ctx == context:
                    print("=" * 20)
                    print("{} ----> {}".format(pprint(x), pprint_value(x.type, eval(x, model))))

            raise Exception("wtf")

        from cozy.cost_model import asymptotic_runtime, is_constant_time
        print("asymptotic cost: {}".format(asymptotic_runtime(new_e_prime)))
        if not is_constant_time(new_e_prime):
            raise NotEfficient(new_e_prime)

        return syntax.SAssign(lval, make_subgoal(new_e_prime))

    s, sgs = sketch_update(lval, e, new_e, ctx=abstract_state, assumptions=assumptions, invariants=invariants)
    subgoals_out.extend(sgs)
    return s

def value_at(m, k):
    """Make an AST node for m[k]."""
    if isinstance(m, target_syntax.EMakeMap2):
        return syntax.ECond(
            syntax.EIn(k, m.e),
            apply(m.value, k),
            construct_value(m.type.v)).with_type(m.type.v)
    if isinstance(m, syntax.ECond):
        return syntax.ECond(
            m.cond,
            value_at(m.then_branch, k),
            value_at(m.else_branch, k)).with_type(m.type.v)
    return target_syntax.EMapGet(m, k).with_type(m.type.v)

def sketch_update(
        lval        : syntax.Exp,
        old_value   : syntax.Exp,
        new_value   : syntax.Exp,
        ctx         : [syntax.EVar],
        assumptions : [syntax.Exp] = [],
        invariants  : [syntax.Exp] = []) -> (syntax.Stm, [syntax.Query]):
    """
    Write code to update `lval` when it changes from `old_value` to `new_value`.
    Variables in `ctx` are assumed to be part of the data structure abstract
    state, and `assumptions` will be appended to all generated subgoals.

    This function returns a statement (code to update `lval`) and a list of
    subgoals (new queries that appear in the code).
    """

    if valid(syntax.EImplies(
            syntax.EAll(itertools.chain(assumptions, invariants)),
            syntax.EEq(old_value, new_value))):
        return (syntax.SNoOp(), [])

    subgoals = []
    new_value = strip_EStateVar(new_value)

    def make_subgoal(e, a=[], docstring=None):
        if skip_stateless_synthesis.value and not any(v in ctx for v in free_vars(e)):
            return e
        query_name = fresh_name("query")
        query = syntax.Query(query_name, syntax.Visibility.Internal, [], assumptions + a, e, docstring)
        query_vars = [v for v in free_vars(query) if v not in ctx]
        query.args = [(arg.id, arg.type) for arg in query_vars]
        subgoals.append(query)
        return syntax.ECall(query_name, tuple(query_vars)).with_type(e.type)

    def recurse(*args, **kwargs):
        (code, sgs) = sketch_update(*args, **kwargs)
        subgoals.extend(sgs)
        return code

    t = lval.type
    if isinstance(t, syntax.TBag) or isinstance(t, syntax.TSet):
        to_add = make_subgoal(syntax.EBinOp(new_value, "-", old_value).with_type(t), docstring="additions to {}".format(pprint(lval)))
        to_del = make_subgoal(syntax.EBinOp(old_value, "-", new_value).with_type(t), docstring="deletions from {}".format(pprint(lval)))
        v = fresh_var(t.t)
        stm = syntax.seq([
            syntax.SForEach(v, to_del, syntax.SCall(lval, "remove", [v])),
            syntax.SForEach(v, to_add, syntax.SCall(lval, "add", [v]))])
    elif is_numeric(t) and update_numbers_with_deltas.value:
        change = make_subgoal(syntax.EBinOp(new_value, "-", old_value).with_type(t), docstring="delta for {}".format(pprint(lval)))
        stm = syntax.SAssign(lval, syntax.EBinOp(lval, "+", change).with_type(t))
    elif isinstance(t, syntax.TTuple):
        get = lambda val, i: syntax.ETupleGet(val, i).with_type(t.ts[i])
        stm = syntax.seq([
            recurse(get(lval, i), get(old_value, i), get(new_value, i), ctx, assumptions,
                invariants=invariants)
            for i in range(len(t.ts))])
    elif isinstance(t, syntax.TRecord):
        get = lambda val, i: syntax.EGetField(val, t.fields[i][0]).with_type(t.fields[i][1])
        stm = syntax.seq([
            recurse(get(lval, i), get(old_value, i), get(new_value, i), ctx, assumptions,
                invariants=invariants)
            for i in range(len(t.fields))])
    elif isinstance(t, syntax.TMap):
        k = fresh_var(lval.type.k)
        v = fresh_var(lval.type.v)
        key_bag = syntax.TBag(lval.type.k)

        old_keys = target_syntax.EMapKeys(old_value).with_type(key_bag)
        new_keys = target_syntax.EMapKeys(new_value).with_type(key_bag)

        # (1) exit set
        deleted_keys = syntax.EBinOp(old_keys, "-", new_keys).with_type(key_bag)
        s1 = syntax.SForEach(k, make_subgoal(deleted_keys, docstring="keys removed from {}".format(pprint(lval))),
            target_syntax.SMapDel(lval, k))

        # (2) enter/mod set
        new_or_modified = target_syntax.EFilter(new_keys,
            syntax.ELambda(k, syntax.EAny([syntax.ENot(syntax.EIn(k, old_keys)), syntax.ENot(syntax.EEq(value_at(old_value, k), value_at(new_value, k)))]))).with_type(key_bag)
        update_value = recurse(
            v,
            value_at(old_value, k),
            value_at(new_value, k),
            ctx = ctx,
            assumptions = assumptions + [syntax.EIn(k, new_or_modified), syntax.EEq(v, value_at(old_value, k))],
            invariants = invariants)
        s2 = syntax.SForEach(k, make_subgoal(new_or_modified, docstring="new or modified keys from {}".format(pprint(lval))),
            target_syntax.SMapUpdate(lval, k, v, update_value))

        stm = syntax.SSeq(s1, s2)
    else:
        # Fallback rule: just compute a new value from scratch
        stm = syntax.SAssign(lval, make_subgoal(new_value, docstring="new value for {}".format(pprint(lval))))

    return (stm, subgoals)


_SOLVERS = { }
def solver_for(context):
    s = _SOLVERS.get(context)
    if s is None:
        s = ModelCachingSolver(
            vars=[v for v, p in context.vars()],
            funcs=context.funcs())
        _SOLVERS[context] = s
    return s

# def optimize_lambda(f, bag, context, pc):
#     context = UnderBinder(context, f.arg, bag, RUNTIME_POOL)
#     return syntax.ELambda(f.arg,
#         optimize(f.body, context, syntax.EAll([pc, syntax.EIn(f.arg, bag)])))

# def optimize(e, context, pc = syntax.T):
#     from cozy.structures.heaps import EMakeMaxHeap, EMakeMinHeap

#     if isinstance(e, int) or isinstance(e, float) or isinstance(e, str):
#         return e

#     if isinstance(e, tuple):
#         return tuple(optimize(x, context, pc) for x in e)

#     if isinstance(e, target_syntax.EStateVar):
#         return e

#     solver = solver_for(context)
#     if e.type == syntax.BOOL:
#         if solver.valid(syntax.EImplies(pc, e)):
#             return syntax.T
#         if solver.valid(syntax.EImplies(pc, syntax.ENot(e))):
#             return syntax.F
#     if is_collection(e.type):
#         if solver.valid(syntax.EImplies(pc, syntax.EEmpty(e))):
#             return syntax.EEmptyList().with_type(e.type)

#     if not isinstance(e, syntax.Exp):
#         raise NotImplementedError(repr(e))

#     # (1) recurse
#     if isinstance(e, target_syntax.EFilter):
#         new_children = [
#             optimize(e.e, context, pc),
#             optimize_lambda(e.p, e.e, context, pc)]
#     elif isinstance(e, target_syntax.EMap) or isinstance(e, target_syntax.EFlatMap) or isinstance(e, syntax.EArgMin) or isinstance(e, syntax.EArgMax) or isinstance(e, EMakeMaxHeap) or isinstance(e, EMakeMinHeap):
#         new_children = [
#             optimize(e.e, context, pc),
#             optimize_lambda(e.f, e.e, context, pc)]
#     elif isinstance(e, target_syntax.ELet):
#         new_children = [
#             optimize(e.e, context, pc),
#             optimize_lambda(e.f, syntax.ESingleton(e.e).with_type(syntax.TBag(e.e.type)), context, pc)]
#     elif isinstance(e, syntax.ECond):
#         new_children = [
#             optimize(e.cond, context, pc),
#             optimize(e.then_branch, context, syntax.EAll([pc, e.cond])),
#             optimize(e.then_branch, context, syntax.EAll([pc, syntax.ENot(e.cond)]))]
#     elif isinstance(e, syntax.EBinOp) and e.op == syntax.BOp.And:
#         new_children = [
#             optimize(e.e1, context, pc),
#             e.op,
#             optimize(e.e2, context, syntax.EAll([pc, e.e1]))]
#     elif isinstance(e, syntax.EBinOp) and e.op == syntax.BOp.Or:
#         new_children = [
#             optimize(e.e1, context, pc),
#             e.op,
#             optimize(e.e2, context, syntax.EAll([pc, syntax.ENot(e.e1)]))]
#     else:
#         assert not any(isinstance(x, target_syntax.ELambda) for x in e.children()), pprint(e)
#         new_children = [optimize(c, context, pc) for c in e.children()]

#     # (2) optimize
#     if isinstance(e, target_syntax.EMap):
#         bag, func = new_children
#         if func.arg == func.body:
#             return bag
#         if isinstance(bag, syntax.ESingleton):
#             return syntax.ESingleton(optimize(apply(func, bag.e), context, pc)).with_type(e.type)
#         if isinstance(bag, syntax.EBinOp) and bag.op == "+":
#             return optimize(syntax.EBinOp(
#                 target_syntax.EMap(bag.e1, func).with_type(e.type), bag.op,
#                 target_syntax.EMap(bag.e2, func).with_type(e.type)).with_type(e.type), context, pc)
#         if isinstance(bag, syntax.EBinOp) and bag.op == "-" and solver.valid(target_syntax.EIsSubset(bag.e2, bag.e1)):
#             return optimize(syntax.EBinOp(
#                 target_syntax.EMap(bag.e1, func).with_type(e.type), bag.op,
#                 target_syntax.EMap(bag.e2, func).with_type(e.type)).with_type(e.type), context, pc)
#     if isinstance(e, target_syntax.EFilter):
#         bag, pred = new_children
#         if e.p.body == syntax.T:
#             return bag
#         if e.p.body == syntax.F:
#             return syntax.EEmptyList().with_type(e.type)
#         if isinstance(bag, syntax.EBinOp) and bag.op in ("+", "-"):
#             return optimize(syntax.EBinOp(
#                 target_syntax.EFilter(bag.e1, pred).with_type(e.type), bag.op,
#                 target_syntax.EFilter(bag.e2, pred).with_type(e.type)).with_type(e.type), context, pc)
#         if isinstance(bag, syntax.ESingleton):
#             return cond(
#                 optimize(apply(pred, bag.e), context, pc),
#                 bag,
#                 syntax.EEmptyList().with_type(e.type))
#     if isinstance(e, syntax.EBinOp):
#         if e.op == syntax.BOp.And:
#             return syntax.EAll([new_children[0], new_children[2]])
#         if e.op == syntax.BOp.Or:
#             return syntax.EAny([new_children[0], new_children[2]])
#     if isinstance(e, syntax.EGetField):
#         record, field_name = new_children
#         if isinstance(record, syntax.EMakeRecord):
#             return dict(record.fields)[field_name]
#     if isinstance(e, syntax.EBinOp) and e.op == "+":
#         e1, _, e2 = new_children
#         if isinstance(e1, syntax.EEmptyList) or e1 == syntax.ZERO:
#             return e2
#         if isinstance(e2, syntax.EEmptyList) or e2 == syntax.ZERO:
#             return e1

#     return type(e)(*new_children).with_type(e.type)

def test():
    return

    import sys
    from cozy.parse import parse_exp, parse_stm
    from cozy.desugar import desugar_list_comprehensions
    from cozy.contexts import RootCtx
    from cozy.syntax import EVar, INT, INT_BAG, TFunc
    from cozy.typecheck import retypecheck
    from cozy.cost_model import asymptotic_runtime

    context = RootCtx(
        state_vars=[EVar("xs").with_type(INT_BAG), EVar("ys").with_type(INT_BAG)],
        args=[EVar("arg").with_type(INT), EVar("arg2").with_type(INT)],
        funcs={
            "f": TFunc((INT,), INT),
            "g": TFunc((INT,), INT),
        })

    type_env = { v.id : v.type for v, p in context.vars() }

    def read_exp(s):
        e = parse_exp(s)
        assert retypecheck(e, env=type_env, fenv=context.funcs())
        return desugar_list_comprehensions(e)

    def read_stm(s):
        s = parse_stm(s)
        assert retypecheck(s, env=type_env, fenv=context.funcs())
        return desugar_list_comprehensions(s)

        e = to_bag(read_exp("[ x | x <- xs, x == 0 ]"))
        s = read_stm("xs.add(arg);")

    cases = [
        # (to_bag(read_exp("[ x | x <- xs, x != 0 ]")),
        #     read_stm("xs.add(arg);")),
        # (read_exp("min [ x | x <- xs, x != 0 ]"),
        #     read_stm("xs.add(arg);")),
        # (read_exp("min xs"),
        #     read_stm("xs.remove(arg);")),
        # (read_exp("min [ x | x <- xs, x != 0 ]"),
        #     read_stm("xs.remove(arg);")),
        # (read_exp("min [ x | x <- xs, x != 0 ]"),
        #     read_stm("xs.remove(arg); xs.add(arg2);")),
        # (read_exp("min [ x | x <- xs, g(x) == arg2 ]"),
        #     read_stm("xs.remove(g(arg));")),
        (read_exp("min [ max [f(y) | y <- ys, g(y) == x] | x <- distinct xs ]"),
            read_stm("ys.remove(arg); ys.add(arg2);"),
            read_exp("g(arg) == g(arg2)")),
        ]

    reses = []
    for e, s, *a in cases:
        try:
            reses.append(better_mutate(
                e=statevar(e),
                context=context,
                op=s,
                assumptions=syntax.EAll(a)))
        except NotEfficient as exc:
            reses.append("(not efficient: {})".format(pprint(exc.expression)))

    print("=" * 40 + " report")
    for i, ((e, s, *a), res) in enumerate(zip(cases, reses)):
        print("-" * 20 + " case {}/{}".format(i+1, len(cases)))
        print(pprint(e))
        print(pprint(s))
        print(pprint(res))
        if isinstance(res, syntax.Exp):
            m = mutate(e, s)
            # print(pprint(partial_eval(mutate(e, s))))
            print("runtime: {}".format(asymptotic_runtime(res)))
            print("    (vs: {})".format(asymptotic_runtime(m)))
            check_valid(context, syntax.EImplies(syntax.EAll(a), syntax.EEq(m, res)), debug={
                "mutated": m,
                "'better'": res,
                })

    sys.exit(0)

def as_first_order_function(e):
    if any(isinstance(x, syntax.ELambda) for x in e.children()):
        raise ValueError(pprint(e))
    if isinstance(e, syntax.EUnaryOp):
        return (lambda e1: syntax.EUnaryOp(e.op, e1).with_type(e.type),
            (e.e,))
    if isinstance(e, syntax.ESingleton):
        return (lambda e1: syntax.ESingleton(e1).with_type(e.type),
            (e.e,))
    if isinstance(e, syntax.EBinOp):
        return (lambda e1, e2: syntax.EBinOp(e1, e.op, e2).with_type(e.type),
            (e.e1, e.e2))
    if isinstance(e, syntax.ECond):
        return (lambda e1, e2, e3: syntax.ECond(e1, e2, e3).with_type(e.type),
            (e.cond, e.then_branch, e.else_branch))
    if isinstance(e, syntax.ECall):
        return (lambda *args: syntax.ECall(e.func, *args).with_type(e.type),
            tuple(e.args))
    raise NotImplementedError(e)

def changed_by(e, s):
    if alpha_equivalent(e, mutate(e, s)):
        return False
    return MAYBE

def unchanged(e, s):
    return invert(changed_by(e, s))

def analyze_changes(f, context, s, assumptions):
    # assert mutate(f.arg, s) == f.arg
    # assert context.legal_for(free_vars(f))

    empty = syntax.EEmptyList().with_type(syntax.TBag(f.arg.type))
    if alpha_equivalent(f, mutate(f, s)):
        return empty

    body = f.body

    try:
        e, args = as_first_order_function(body)
        results = [analyze_changes(syntax.ELambda(f.arg, x), context, s, assumptions) for x in args]
        out = empty
        for r in results:
            out = bag_union(out, r)
        return out
    except ValueError:
        pass

    if isinstance(body, target_syntax.EMap) and body.f.arg == body.f.body:
        return analyze_changes(syntax.ELambda(f.arg, body.e), context, s, assumptions)

    e = body
    if isinstance(e, target_syntax.EFilter):
        if f.arg not in free_vars(e.e):
            for cond in break_conj(nnf(e.p.body)):
                if isinstance(cond, syntax.EBinOp) and cond.op in ("==", "==="):
                    for x, y in [(cond.e1, cond.e2), (cond.e2, cond.e1)]:
                        fvx = free_vars(x)
                        fvy = free_vars(y)
                        if e.p.arg in fvx and e.p.arg not in fvy:
                            # domain = e.e
                            # proj = syntax.ELambda(e.p.arg, x)
                            # g = syntax.ELambda(e.p.arg, y)
                            # res = mk_lambda(e.type, lambda x: x)
                            n, d = bag_delta(e.e, context, s, assumptions)
                            # print("enter: {}".format(pprint(n)))
                            # print("exit: {}".format(pprint(d)))
                            # print("p: {}".format(pprint(e.p)))
                            return bag_union(
                                emap(d, syntax.ELambda(e.p.arg, x)),
                                emap(n, syntax.ELambda(e.p.arg, x)))

    if isinstance(e, target_syntax.EArgMin) or isinstance(e, target_syntax.EArgMax) or isinstance(e, target_syntax.EMap):
        if definitely(unchanged(e.f, s)):
            return analyze_changes(syntax.ELambda(f.arg, e.e), context, s, assumptions)

    raise NotImplementedError("{} / {}".format(type(body), pprint(body)))

def run():
    verbose.value = True

    from cozy.syntax import EVar, SNoOp, TNative, TEnum, EGetField, TRecord, TInt, ELambda, EBinOp, TBool, TBag, SAssign, SSeq, SIf, TMap, SCall, ESingleton, EMakeRecord, TList, EUnaryOp, ECall, EArgMin, EArgMax, ENum, SDecl, EEnumEntry, EAll, TSet, TFunc, ECond, EEmptyList, EImplies, ENot, EIn, EEq
    from cozy.target_syntax import EMap, EFilter, EMakeMap2, EStateVar, EFlatMap
    from cozy.contexts import RootCtx
    from cozy.pools import RUNTIME_POOL

    s = SSeq(SDecl('c', EUnaryOp('the', EMap(EFilter(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_iface').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), '==', EVar('i').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*'))).with_type(TBool()))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TList(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), SSeq(SCall(EVar('_idleHosts').with_type(TBag(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t')))))), 'remove_all', (EMap(EFilter(EVar('_idleHosts').with_type(TBag(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t')))))), ELambda(EVar('h').with_type(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t'))))), EBinOp(EGetField(EVar('h').with_type(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t'))))), 'host_id').with_type(TNative('mongo::HostAndPort')), '==', EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort'))).with_type(TBool()))).with_type(TBag(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t')))))), ELambda(EVar('h').with_type(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t'))))), EVar('h').with_type(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t'))))))).with_type(TList(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t')))))),)), SSeq(SCall(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), 'remove', (EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))),)), SSeq(SCall(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), 'add', (EMakeRecord((('conn_state', EEnumEntry('READY').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT')))), ('conn_host', EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort'))), ('conn_iface', EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_iface').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*'))), ('conn_next_refresh', ECall('after', (EVar('lastUsed').with_type(TNative('mongo::Date_t')), EVar('refreshRequirement').with_type(TNative('mongo::Milliseconds')))).with_type(TNative('mongo::Date_t'))), ('conn_returned', EVar('now').with_type(TNative('mongo::Date_t'))), ('conn_last_used', EVar('retId').with_type(TInt())), ('conn_dropped', EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_dropped').with_type(TBool())))).with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))),)), SSeq(SIf(EUnaryOp('not', EBinOp(EUnaryOp('exists', EMap(EFilter(EVar('reqs').with_type(TBag(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort')))))), ELambda(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), EBinOp(EGetField(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), 'rq_host').with_type(TNative('mongo::HostAndPort')), '==', EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort'))).with_type(TBool()))).with_type(TBag(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort')))))), ELambda(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))))).with_type(TList(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))))).with_type(TBool()), 'or', EUnaryOp('exists', EMap(EFilter(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('_var6546').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EBinOp(EGetField(EVar('_var6546').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort')), '==', EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort'))).with_type(TBool()), 'and', EBinOp(EGetField(EVar('_var6546').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_state').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), '==', EEnumEntry('CHECKED_OUT').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT')))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('_var6547').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EVar('_var6547').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TList(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TBool())).with_type(TBool())).with_type(TBool()), SCall(EVar('_idleHosts').with_type(TBag(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t')))))), 'add', (EMakeRecord((('host_id', EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort'))), ('host_timeout', ECall('after', (EArgMax(EMap(EMap(EFilter(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('_var6549').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EBinOp(EGetField(EVar('_var6549').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort')), '==', EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort'))).with_type(TBool()), 'and', EBinOp(EGetField(EVar('_var6549').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_state').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), '!=', EEnumEntry('CHECKED_OUT').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT')))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('_var6550').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EVar('_var6550').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TList(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('_var6548').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EGetField(EVar('_var6548').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_returned').with_type(TNative('mongo::Date_t')))).with_type(TList(TNative('mongo::Date_t'))), ELambda(EVar('x').with_type(TNative('mongo::Date_t')), EVar('x').with_type(TNative('mongo::Date_t')))).with_type(TNative('mongo::Date_t')), EVar('hostTimeout').with_type(TNative('mongo::Milliseconds')))).with_type(TNative('mongo::Date_t'))))).with_type(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t'))))),)), SNoOp()), SAssign(EVar('retId').with_type(TInt()), EBinOp(EVar('retId').with_type(TInt()), '+', ENum(1).with_type(TInt())).with_type(TInt())))))))


    # bag = EBinOp(EUnaryOp('distinct', EMap(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort')))).with_type(TList(TNative('mongo::HostAndPort')))).with_type(TList(TNative('mongo::HostAndPort'))), '-', EFilter(EUnaryOp('distinct', EBinOp(EFlatMap(ECond(EBinOp(EUnaryOp('the', EMap(EFilter(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_iface').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), '==', EVar('i').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*'))).with_type(TBool()))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TList(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'in', EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TBool()), ESingleton(EUnaryOp('the', EMap(EFilter(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_iface').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), '==', EVar('i').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*'))).with_type(TBool()))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TList(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), EEmptyList().with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), ESingleton(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort'))).with_type(TList(TNative('mongo::HostAndPort'))))).with_type(TList(TNative('mongo::HostAndPort'))), '+', EFlatMap(EBinOp(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), '-', ESingleton(EUnaryOp('the', EMap(EFilter(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_iface').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), '==', EVar('i').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*'))).with_type(TBool()))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TList(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('_var22').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EEmptyList().with_type(TList(TNative('mongo::HostAndPort'))))).with_type(TList(TNative('mongo::HostAndPort')))).with_type(TList(TNative('mongo::HostAndPort')))).with_type(TList(TNative('mongo::HostAndPort'))), ELambda(EVar('_var24').with_type(TNative('mongo::HostAndPort')), EBinOp(EUnaryOp('len', EFilter(EMap(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort')))).with_type(TList(TNative('mongo::HostAndPort'))), ELambda(EVar('_var25').with_type(TNative('mongo::HostAndPort')), EBinOp(EVar('_var24').with_type(TNative('mongo::HostAndPort')), '==', EVar('_var25').with_type(TNative('mongo::HostAndPort'))).with_type(TBool()))).with_type(TList(TNative('mongo::HostAndPort')))).with_type(TInt()), '==', ENum(1).with_type(TInt())).with_type(TBool()))).with_type(TList(TNative('mongo::HostAndPort')))).with_type(TList(TNative('mongo::HostAndPort')))

    # lval, e, s = (EVar('_var102529').with_type(TMap(TNative('mongo::executor::ConnectionPool::ConnectionInterface*'), TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))), EMakeMap2(EMap(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('_var98754').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EGetField(EVar('_var98754').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_iface').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*')))).with_type(TBag(TNative('mongo::executor::ConnectionPool::ConnectionInterface*'))), ELambda(EVar('_key98752').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), EFilter(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_iface').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), '==', EVar('_key98752').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*'))).with_type(TBool()))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))))).with_type(TMap(TNative('mongo::executor::ConnectionPool::ConnectionInterface*'), TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))), SSeq(SDecl('c', EUnaryOp('the', EMap(EFilter(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_iface').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), '==', EVar('i').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*'))).with_type(TBool()))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), SSeq(SCall(EVar('_idleHosts').with_type(TBag(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t')))))), 'remove_all', (EMap(EFilter(EVar('_idleHosts').with_type(TBag(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t')))))), ELambda(EVar('h').with_type(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t'))))), EBinOp(EGetField(EVar('h').with_type(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t'))))), 'host_id').with_type(TNative('mongo::HostAndPort')), '==', EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort'))).with_type(TBool()))).with_type(TBag(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t')))))), ELambda(EVar('h').with_type(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t'))))), EVar('h').with_type(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t'))))))).with_type(TBag(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t')))))),)), SSeq(SCall(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), 'remove', (EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))),)), SSeq(SAssign(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), EBinOp(ESingleton(EMakeRecord((('conn_state', EEnumEntry('READY').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT')))), ('conn_host', EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort'))), ('conn_iface', EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_iface').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*'))), ('conn_next_refresh', ECall('after', (EVar('lastUsed').with_type(TNative('mongo::Date_t')), EVar('refreshRequirement').with_type(TNative('mongo::Milliseconds')))).with_type(TNative('mongo::Date_t'))), ('conn_returned', EVar('now').with_type(TNative('mongo::Date_t'))), ('conn_last_used', EVar('retId').with_type(TInt())), ('conn_dropped', EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_dropped').with_type(TBool())))).with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))).with_type(TList(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), '+', EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TList(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))), SSeq(SIf(EUnaryOp('not', EBinOp(EUnaryOp('exists', EMap(EFilter(EVar('reqs').with_type(TBag(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort')))))), ELambda(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), EBinOp(EGetField(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), 'rq_host').with_type(TNative('mongo::HostAndPort')), '==', EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort'))).with_type(TBool()))).with_type(TBag(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort')))))), ELambda(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))))).with_type(TBag(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))))).with_type(TBool()), 'or', EUnaryOp('exists', EMap(EFilter(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('_var3771').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EBinOp(EGetField(EVar('_var3771').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort')), '==', EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort'))).with_type(TBool()), 'and', EBinOp(EGetField(EVar('_var3771').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_state').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), '==', EEnumEntry('CHECKED_OUT').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT')))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('_var3772').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EVar('_var3772').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TBool())).with_type(TBool())).with_type(TBool()), SCall(EVar('_idleHosts').with_type(TBag(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t')))))), 'add', (EMakeRecord((('host_id', EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort'))), ('host_timeout', ECall('after', (EArgMax(EMap(EFilter(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('_var3773').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EBinOp(EGetField(EVar('_var3773').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort')), '==', EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort'))).with_type(TBool()), 'and', EBinOp(EGetField(EVar('_var3773').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_state').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), '!=', EEnumEntry('CHECKED_OUT').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT')))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('_var3774').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EGetField(EVar('_var3774').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_returned').with_type(TNative('mongo::Date_t')))).with_type(TBag(TNative('mongo::Date_t'))), ELambda(EVar('x').with_type(TNative('mongo::Date_t')), EVar('x').with_type(TNative('mongo::Date_t')))).with_type(TNative('mongo::Date_t')), EVar('hostTimeout').with_type(TNative('mongo::Milliseconds')))).with_type(TNative('mongo::Date_t'))))).with_type(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t'))))),)), SNoOp()), SAssign(EVar('retId').with_type(TInt()), EBinOp(EVar('retId').with_type(TInt()), '+', ENum(1).with_type(TInt())).with_type(TInt()))))))))

    lval = EVar('_var22838').with_type(TNative('mongo::Date_t'))

    # _idlehosts bar nonsense
    # e = EArgMin(EMap(EVar('_idleHosts').with_type(TBag(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t')))))), ELambda(EVar('h').with_type(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t'))))), EGetField(EVar('h').with_type(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t'))))), 'host_timeout').with_type(TNative('mongo::Date_t')))).with_type(TList(TNative('mongo::Date_t'))), ELambda(EVar('x').with_type(TNative('mongo::Date_t')), EVar('x').with_type(TNative('mongo::Date_t')))).with_type(TNative('mongo::Date_t'))

    # nextEvent
    e = EArgMin(EBinOp(EBinOp(EMap(EVar('reqs').with_type(TBag(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort')))))), ELambda(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), EGetField(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), 'rq_expiration').with_type(TNative('mongo::Date_t')))).with_type(TList(TNative('mongo::Date_t'))), '+', EMap(EFilter(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_state').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), '==', EEnumEntry('READY').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT')))).with_type(TBool()))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_next_refresh').with_type(TNative('mongo::Date_t')))).with_type(TList(TNative('mongo::Date_t')))).with_type(TList(TNative('mongo::Date_t'))), '+', EMap(EMap(EFilter(EUnaryOp('distinct', EMap(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort')))).with_type(TList(TNative('mongo::HostAndPort')))).with_type(TList(TNative('mongo::HostAndPort'))), ELambda(EVar('p').with_type(TNative('mongo::HostAndPort')), EUnaryOp('not', EBinOp(EUnaryOp('exists', EMap(EFilter(EVar('reqs').with_type(TBag(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort')))))), ELambda(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), EBinOp(EGetField(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), 'rq_host').with_type(TNative('mongo::HostAndPort')), '==', EVar('p').with_type(TNative('mongo::HostAndPort'))).with_type(TBool()))).with_type(TBag(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort')))))), ELambda(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))))).with_type(TList(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))))).with_type(TBool()), 'or', EUnaryOp('exists', EMap(EFilter(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort')), '==', EVar('p').with_type(TNative('mongo::HostAndPort'))).with_type(TBool()), 'and', EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_state').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), '==', EEnumEntry('CHECKED_OUT').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT')))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TList(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TBool())).with_type(TBool())).with_type(TBool()))).with_type(TList(TNative('mongo::HostAndPort'))), ELambda(EVar('p').with_type(TNative('mongo::HostAndPort')), EVar('p').with_type(TNative('mongo::HostAndPort')))).with_type(TList(TNative('mongo::HostAndPort'))), ELambda(EVar('p').with_type(TNative('mongo::HostAndPort')), ECall('after', (EArgMax(EMap(EMap(EFilter(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort')), '==', EVar('p').with_type(TNative('mongo::HostAndPort'))).with_type(TBool()), 'and', EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_state').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), '!=', EEnumEntry('CHECKED_OUT').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT')))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TList(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_returned').with_type(TNative('mongo::Date_t')))).with_type(TList(TNative('mongo::Date_t'))), ELambda(EVar('x').with_type(TNative('mongo::Date_t')), EVar('x').with_type(TNative('mongo::Date_t')))).with_type(TNative('mongo::Date_t')), EVar('hostTimeout').with_type(TNative('mongo::Milliseconds')))).with_type(TNative('mongo::Date_t')))).with_type(TList(TNative('mongo::Date_t')))).with_type(TList(TNative('mongo::Date_t'))), ELambda(EVar('x').with_type(TNative('mongo::Date_t')), EVar('x').with_type(TNative('mongo::Date_t')))).with_type(TNative('mongo::Date_t'))

    # nextEvent using _idleHosts
    # e = EArgMin(EBinOp(EBinOp(EMap(EVar('reqs').with_type(TBag(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort')))))), ELambda(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), EGetField(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), 'rq_expiration').with_type(TNative('mongo::Date_t')))).with_type(TList(TNative('mongo::Date_t'))), '+', EMap(EFilter(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_state').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), '==', EEnumEntry('READY').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT')))).with_type(TBool()))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_next_refresh').with_type(TNative('mongo::Date_t')))).with_type(TList(TNative('mongo::Date_t')))).with_type(TList(TNative('mongo::Date_t'))), '+', EMap(EVar('_idleHosts').with_type(TBag(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t')))))), ELambda(EVar('h').with_type(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t'))))), EGetField(EVar('h').with_type(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t'))))), 'host_timeout').with_type(TNative('mongo::Date_t')))).with_type(TList(TNative('mongo::Date_t')))).with_type(TList(TNative('mongo::Date_t'))), ELambda(EVar('x').with_type(TNative('mongo::Date_t')), EVar('x').with_type(TNative('mongo::Date_t')))).with_type(TNative('mongo::Date_t'))

    # nextEvent computing idleHosts by subtraction
    # e = EArgMin(EBinOp(EBinOp(EMap(EVar('reqs').with_type(TBag(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort')))))), ELambda(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), EGetField(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), 'rq_expiration').with_type(TNative('mongo::Date_t')))).with_type(TList(TNative('mongo::Date_t'))), '+', EMap(EFilter(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_state').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), '==', EEnumEntry('READY').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT')))).with_type(TBool()))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_next_refresh').with_type(TNative('mongo::Date_t')))).with_type(TList(TNative('mongo::Date_t')))).with_type(TList(TNative('mongo::Date_t'))), '+', EMap(EBinOp(EUnaryOp('distinct', EMap(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort')))).with_type(TList(TNative('mongo::HostAndPort')))).with_type(TList(TNative('mongo::HostAndPort'))), '-', EUnaryOp('distinct', EMap(EFilter(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_state').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), '==', EEnumEntry('CHECKED_OUT').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT')))).with_type(TBool()), 'or', EUnaryOp('exists', EMap(EFilter(EVar('reqs').with_type(TSet(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort')))))), ELambda(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), EBinOp(EGetField(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), 'rq_host').with_type(TNative('mongo::HostAndPort')), '==', EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort'))).with_type(TBool()))).with_type(TSet(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort')))))), ELambda(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))))).with_type(TList(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort')))).with_type(TList(TNative('mongo::HostAndPort')))).with_type(TList(TNative('mongo::HostAndPort')))).with_type(TList(TNative('mongo::HostAndPort'))), ELambda(EVar('p').with_type(TNative('mongo::HostAndPort')), ECall('after', (EArgMax(EMap(EMap(EFilter(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort')), '==', EVar('p').with_type(TNative('mongo::HostAndPort'))).with_type(TBool()), 'and', EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_state').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), '!=', EEnumEntry('CHECKED_OUT').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT')))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TList(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_returned').with_type(TNative('mongo::Date_t')))).with_type(TList(TNative('mongo::Date_t'))), ELambda(EVar('x').with_type(TNative('mongo::Date_t')), EVar('x').with_type(TNative('mongo::Date_t')))).with_type(TNative('mongo::Date_t')), EVar('hostTimeout').with_type(TNative('mongo::Milliseconds')))).with_type(TNative('mongo::Date_t')))).with_type(TList(TNative('mongo::Date_t')))).with_type(TList(TNative('mongo::Date_t'))), ELambda(EVar('x').with_type(TNative('mongo::Date_t')), EVar('x').with_type(TNative('mongo::Date_t')))).with_type(TNative('mongo::Date_t'))

    # some dumb map
    # e = EMakeMap2(EMap(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_iface').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*')))).with_type(TBag(TNative('mongo::executor::ConnectionPool::ConnectionInterface*'))), ELambda(EVar('_var28533').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), EGetField(EUnaryOp('the', EFilter(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_iface').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), '==', EVar('_var28533').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*'))).with_type(TBool()))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_dropped').with_type(TBool()))).with_type(TMap(TNative('mongo::executor::ConnectionPool::ConnectionInterface*'), TBool()))

    assumptions = [
        EUnaryOp('unique', EMap(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_iface').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*')))).with_type(TList(TNative('mongo::executor::ConnectionPool::ConnectionInterface*')))).with_type(TBool()),
        EUnaryOp('all', EMap(EFilter(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_state').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), '==', EEnumEntry('READY').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT')))).with_type(TBool()))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_last_used').with_type(TInt()), '<', EVar('retId').with_type(TInt())).with_type(TBool()))).with_type(TList(TBool()))).with_type(TBool()),
        EUnaryOp('unique', EMap(EVar('reqs').with_type(TBag(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort')))))), ELambda(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), EGetField(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), 'rq_callback').with_type(TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')))).with_type(TList(TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')))).with_type(TBool()),
        EBinOp(EVar('_idleHosts').with_type(TBag(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t')))))), '==', EMap(EMap(EFilter(EUnaryOp('distinct', EMap(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort')))).with_type(TList(TNative('mongo::HostAndPort')))).with_type(TList(TNative('mongo::HostAndPort'))), ELambda(EVar('p').with_type(TNative('mongo::HostAndPort')), EUnaryOp('not', EBinOp(EUnaryOp('exists', EMap(EFilter(EVar('reqs').with_type(TBag(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort')))))), ELambda(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), EBinOp(EGetField(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), 'rq_host').with_type(TNative('mongo::HostAndPort')), '==', EVar('p').with_type(TNative('mongo::HostAndPort'))).with_type(TBool()))).with_type(TBag(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort')))))), ELambda(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))))).with_type(TList(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))))).with_type(TBool()), 'or', EUnaryOp('exists', EMap(EFilter(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort')), '==', EVar('p').with_type(TNative('mongo::HostAndPort'))).with_type(TBool()), 'and', EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_state').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), '==', EEnumEntry('CHECKED_OUT').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT')))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TList(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TBool())).with_type(TBool())).with_type(TBool()))).with_type(TList(TNative('mongo::HostAndPort'))), ELambda(EVar('p').with_type(TNative('mongo::HostAndPort')), EVar('p').with_type(TNative('mongo::HostAndPort')))).with_type(TList(TNative('mongo::HostAndPort'))), ELambda(EVar('p').with_type(TNative('mongo::HostAndPort')), EMakeRecord((('host_id', EVar('p').with_type(TNative('mongo::HostAndPort'))), ('host_timeout', ECall('after', (EArgMax(EMap(EMap(EFilter(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort')), '==', EVar('p').with_type(TNative('mongo::HostAndPort'))).with_type(TBool()), 'and', EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_state').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), '!=', EEnumEntry('CHECKED_OUT').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT')))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TList(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_returned').with_type(TNative('mongo::Date_t')))).with_type(TList(TNative('mongo::Date_t'))), ELambda(EVar('x').with_type(TNative('mongo::Date_t')), EVar('x').with_type(TNative('mongo::Date_t')))).with_type(TNative('mongo::Date_t')), EVar('hostTimeout').with_type(TNative('mongo::Milliseconds')))).with_type(TNative('mongo::Date_t'))))).with_type(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t'))))))).with_type(TList(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t'))))))).with_type(TBool()),
        EUnaryOp('unique', EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TBool()),
        EUnaryOp('unique', EVar('reqs').with_type(TBag(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))))).with_type(TBool()),
        EUnaryOp('unique', EVar('_idleHosts').with_type(TBag(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t'))))))).with_type(TBool()),

        EUnaryOp('exists', EMap(EFilter(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_iface').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), '==', EVar('i').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*'))).with_type(TBool()))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TList(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TBool()),
        EBinOp(EGetField(EUnaryOp('the', EMap(EFilter(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_iface').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), '==', EVar('i').with_type(TNative('mongo::executor::ConnectionPool::ConnectionInterface*'))).with_type(TBool()))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TList(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_state').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), '!=', EEnumEntry('READY').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT')))).with_type(TBool()),
        EUnaryOp('all', EMap(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EVar('now').with_type(TNative('mongo::Date_t')), '>=', EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_returned').with_type(TNative('mongo::Date_t'))).with_type(TBool()))).with_type(TList(TBool()))).with_type(TBool())]

    abstate = [
            EVar('minConnections').with_type(TInt()),
            EVar('maxConnections').with_type(TInt()),
            EVar('maxConnecting').with_type(TInt()),
            EVar('refreshTimeout').with_type(TNative('mongo::Milliseconds')),
            EVar('refreshRequirement').with_type(TNative('mongo::Milliseconds')),
            EVar('hostTimeout').with_type(TNative('mongo::Milliseconds')),
            EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))),
            EVar('reqs').with_type(TBag(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort')))))),
            EVar('_idleHosts').with_type(TBag(TRecord((('host_id', TNative('mongo::HostAndPort')), ('host_timeout', TNative('mongo::Date_t')))))),
            EVar('retId').with_type(TInt())]

    context = RootCtx(
        state_vars=abstate,
        args=[v for v in (free_vars(e) | free_vars(s)) if v not in abstate],
        funcs=OrderedDict([('eternity', TFunc((), TNative('mongo::Date_t'))),
             ('after',
              TFunc((TNative('mongo::Date_t'), TNative('mongo::Milliseconds')), TNative('mongo::Date_t'))),
             ('nullConn',
              TFunc((), TNative('mongo::executor::ConnectionPool::ConnectionInterface*'))),
             ('nullReq',
              TFunc((), TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')))]))

    if False:
        f = ELambda(EVar('_var21').with_type(TNative('mongo::HostAndPort')), ECond(EUnaryOp('not', EBinOp(EUnaryOp('exists', EMap(EFilter(EVar('reqs').with_type(TBag(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort')))))), ELambda(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), EBinOp(EGetField(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), 'rq_host').with_type(TNative('mongo::HostAndPort')), '==', EVar('_var21').with_type(TNative('mongo::HostAndPort'))).with_type(TBool()))).with_type(TBag(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort')))))), ELambda(EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))), EVar('r').with_type(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))))).with_type(TList(TRecord((('rq_callback', TNative('mongo::executor::ConnectionPool::GetConnectionCallback*')), ('rq_expiration', TNative('mongo::Date_t')), ('rq_host', TNative('mongo::HostAndPort'))))))).with_type(TBool()), 'or', EUnaryOp('exists', EMap(EFilter(EVar('conns').with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EBinOp(EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_host').with_type(TNative('mongo::HostAndPort')), '==', EVar('_var21').with_type(TNative('mongo::HostAndPort'))).with_type(TBool()), 'and', EBinOp(EGetField(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), 'conn_state').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), '==', EEnumEntry('CHECKED_OUT').with_type(TEnum(('READY', 'PROCESSING', 'CHECKED_OUT')))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool()))))), ELambda(EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))), EVar('c').with_type(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TList(TRecord((('conn_state', TEnum(('READY', 'PROCESSING', 'CHECKED_OUT'))), ('conn_host', TNative('mongo::HostAndPort')), ('conn_iface', TNative('mongo::executor::ConnectionPool::ConnectionInterface*')), ('conn_next_refresh', TNative('mongo::Date_t')), ('conn_returned', TNative('mongo::Date_t')), ('conn_last_used', TInt()), ('conn_dropped', TBool())))))).with_type(TBool())).with_type(TBool())).with_type(TBool()), ESingleton(EVar('_var21').with_type(TNative('mongo::HostAndPort'))).with_type(TList(TNative('mongo::HostAndPort'))), EEmptyList().with_type(TList(TNative('mongo::HostAndPort')))).with_type(TList(TNative('mongo::HostAndPort'))))
        print(pprint(f))
        print("-" * 20)
        print(pprint(s))
        print("-" * 20)

        ch = analyze_changes(f, context, s, EAll(assumptions))
        print(pprint(ch))
        assert f.arg.type == ch.type.t, "f.arg.type={}, ch.type={}".format(pprint(f.arg.type), pprint(ch.type))

        f_prime = mutate(f, s)
        # bag = fresh_var(TBag(f.arg.type))
        check_valid(context,
            EImplies(ENot(EIn(f.arg, ch)), EEq(f.body, f_prime.body)),
            debug={
            "x": f.arg,
            "f(x)": f.body,
            "f'(x)": f_prime.body,
            "ch": ch,
            })

        print("Ok!")
        return 1

    sqs = []

    print(pprint(e))
    print("-"*40)
    e = partial_eval(e)
    print(pprint(e))
    print("-"*40)
    print("// IN: {}".format(", ".join(v.id for v, p in context.vars() if p == RUNTIME_POOL)))
    print(pprint(s))
    print("-"*40)

    print(pprint(mutate(e, s)))

    print("-"*40)

    # v = EVar("lval").with_type(e.type)
    # subgoals = []
    # update_stm = mutate_in_place(v, e, s, abstate, assumptions, subgoals)
    # print(pprint(update_stm))
    # for g in subgoals:
    #     print(pprint(g))
    # return

    from cozy.solver import break_let

    print("Mutating...")
    e_prime = better_mutate(
        e=EStateVar(e).with_type(e.type),
        context=context,
        op=s,
        assumptions=EAll(assumptions))

    print("Repairing...")
    e_prime = repair_EStateVar_in_context(e_prime, context, available_state=[e])

    # print("Optimizing...")
    # e_prime_opt = optimize(e_prime, context=context, pc=EAll(assumptions))

    print("Unpacking...")
    from cozy.syntax_tools import pack_representation, unpack_representation
    rep, ret = unpack_representation(e_prime)

    print("Eliminating common subexpressions...")
    ret = cse(ret)

    print("-" * 20 + " done!")

    for statevar, stateexp in rep:
        print("state {} = {}".format(pprint(statevar), pprint(stateexp)))

    print("-" * 20)

    for part in break_let(ret):
        if isinstance(part, syntax.Exp):
            print("return {}".format(pprint(part)))
        else:
            var, val = part
            print("{} = {}".format(var.id, pprint(val)))

    print("Packing...")
    e_prime = pack_representation(rep, ret)

    import pickle
    with open("exp.pickle", "wb") as f:
        pickle.dump(e_prime, f)

    # print(pprint(better_mutate(
    #     e=EStateVar(e).with_type(e.type),
    #     context=context,
    #     op=s,
    #     assumptions=EAll(assumptions))))

    return

    print(pprint(mutate_in_place(lval, e, s, abstate, subgoals_out=sqs, assumptions=assumptions)))

    for q in sqs:
        print("-"*40)
        print(pprint(q))

        from cozy.syntax_tools import unpack_representation

        # return

        ret = optimize_to_fixpoint(
            repair_EStateVar(q.ret, abstate),
            context=context,
            validate=True,
            assumptions=EAll(assumptions))
        rep, ret = unpack_representation(ret)
        print(" ---> {}".format(pprint(ret)))

if __name__ == "__main__":
    import sys
    test()
    sys.exit(run() or 0)
