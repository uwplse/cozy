"""Functions for managing stateful computation.

Important functions:
 - mutate: compute the new value of an expression after a statement executes
 - mutate_in_place: write code to keep a derived value in sync with its inputs
"""

import itertools

from cozy.common import fresh_name, typechecked
from cozy import syntax
from cozy import target_syntax
from cozy.syntax_tools import free_vars, pprint, fresh_var, strip_EStateVar, subst, BottomUpRewriter, alpha_equivalent, break_seq
from cozy.typecheck import is_numeric
from cozy.solver import valid
from cozy.opts import Option
from cozy.structures import extension_handler
from cozy.evaluation import construct_value
from cozy.contexts import Context

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
            e2 = subst(e2, { op.s1.id : op.s1.val })
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

@typechecked
def better_mutate(
        e           : target_syntax.EStateVar,
        context     : Context,
        op          : syntax.Stm,
        assumptions : syntax.Exp) -> syntax.Exp:
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
        add, remove = checked_bag_delta(e, op)
        print("{} x {} ---> +{}, -{}".format(pprint(e), pprint(op), pprint(add), pprint(remove)))
        return bag_union(bag_subtract(e, remove), add)

    # if bag:
    #     added+removed
    if isinstance(e, syntax.EArgMin) or isinstance(e, syntax.EArgMax):
        if alpha_equivalent(e.f, mutate(e.f, op)):
            to_add, to_del = checked_bag_delta(target_syntax.EStateVar(e.e).with_type(e.e.type), op)
            from cozy.structures.heaps import to_heap, EHeapPeek2
            h = to_heap(e)
            h = target_syntax.EStateVar(h).with_type(h.type)
            second_min = syntax.ESingleton(EHeapPeek2(h, target_syntax.EStateVar(syntax.ELen(e.e)).with_type(syntax.INT)).with_type(e.type)).with_type(e.e.type)

            v = fresh_var(to_del.type, "removed")

            if isinstance(to_del, syntax.EEmptyList) or valid(syntax.EImplies(assumptions, syntax.EEmpty(to_del))):
                min_after_del = esv
            # elif valid(syntax.EImplies(assumptions, syntax.EEq(syntax.ELen(to_del), syntax.ONE))):
            #     min_after_del = second_min
            elif valid(syntax.EImplies(assumptions, syntax.ELe(syntax.ELen(to_del), syntax.ONE))):
                min_after_del = syntax.ECond(
                    syntax.ELet(
                        to_del,
                        syntax.ELambda(v,
                            syntax.EAll([syntax.EExists(v), syntax.EEq(syntax.EUnaryOp(syntax.UOp.The, v).with_type(e.type), esv)]))).with_type(syntax.BOOL),
                    syntax.ECond(syntax.EGt(target_syntax.EStateVar(syntax.ELen(e.e)).with_type(syntax.INT), syntax.ONE), second_min, syntax.EEmptyList().with_type(e.e.type)).with_type(e.e.type),
                    syntax.ECond(target_syntax.EStateVar(syntax.EExists(e.e)).with_type(syntax.BOOL), syntax.ESingleton(esv).with_type(e.e.type), syntax.EEmptyList().with_type(e.e.type)).with_type(e.e.type)).with_type(e.e.type)
                assert_eq(
                    type(e)(bag_subtract(e.e, to_del), e.f).with_type(e.type),
                    type(e)(min_after_del, e.f).with_type(e.type),
                    context=context,
                    assumptions=assumptions)
            else:
                # ugh, recompute
                print(pprint(assumptions))
                print(pprint(to_del))
                raise NotEfficient(e)
                return mutate(e, op)


            res = type(e)(bag_union(
                min_after_del,
                to_add), e.f).with_type(e.type)

            # from cozy.typecheck import retypecheck
            # assert retypecheck(res)
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

def emap(e, f):
    out_type = type(e.type)(f.body.type)
    if isinstance(e, syntax.EEmptyList):
        return syntax.EEmptyList().with_type(out_type)
    if isinstance(e, syntax.ESingleton):
        return syntax.ESingleton(f.apply_to(e.e)).with_type(out_type)
    if isinstance(e, syntax.EBinOp) and e.op == "+":
        return bag_union(emap(e.e1, f), emap(e.e2, f))
    if isinstance(e, target_syntax.EMap):
        return emap(e.e, compose(f, e.f))
    return target_syntax.EMap(e, f).with_type(out_type)

def efilter(e, f):
    out_type = e.type
    if isinstance(e, syntax.EEmptyList):
        return syntax.EEmptyList().with_type(out_type)
    if isinstance(e, syntax.EBinOp) and e.op == "+":
        return bag_union(efilter(e.e1, f), efilter(e.e2, f))
    if isinstance(e, target_syntax.EMap):
        return efilter(e.e, compose(f, e.f))
    return target_syntax.EFilter(e, f).with_type(out_type)

def bag_union(e1, e2):
    if isinstance(e1, syntax.EEmptyList):
        return e2
    if isinstance(e2, syntax.EEmptyList):
        return e1
    return syntax.EBinOp(e1, "+", e2).with_type(e1.type)

class NotEfficient(Exception):
    def __init__(self, e):
        super().__init__(pprint(e))
        self.expression = e

def bag_contains(bag, x):
    return syntax.EIn(x, bag)

def bag_subtract(e1, e2):
    if isinstance(e1, syntax.EEmptyList):
        return e1
    if isinstance(e2, syntax.EEmptyList):
        return e1
    if alpha_equivalent(e1, e2):
        return syntax.EEmptyList().with_type(e1.type)
    if isinstance(e2, syntax.ECond):
        return syntax.ECond(e2.cond,
            bag_subtract(e1, e2.then_branch),
            bag_subtract(e1, e2.else_branch)).with_type(e1.type)
    if isinstance(e1, syntax.ECond):
        return syntax.ECond(e1.cond,
            bag_subtract(e1.then_branch, e2),
            bag_subtract(e1.else_branch, e2)).with_type(e1.type)
    if isinstance(e1, syntax.EBinOp) and e1.op == "+" and alpha_equivalent(e1.e1, e2):
        return e1.e2
    if isinstance(e2, syntax.EBinOp) and e2.op == "+" and alpha_equivalent(e1, e2.e1):
        return syntax.EEmptyList().with_type(e1.type)
    if isinstance(e1, syntax.EBinOp) and e1.op == "-" and alpha_equivalent(e1.e1, e2):
        return syntax.EEmptyList().with_type(e1.type)
    if isinstance(e2, syntax.EBinOp) and e2.op == "-" and alpha_equivalent(e2.e1, e1) and isinstance(e2.e2, syntax.ESingleton):
        return cond(bag_contains(e1, e2.e2.e), e2.e2, syntax.EEmptyList().with_type(e1.type))
    # if isinstance(e1, syntax.EBinOp) and e1.op == "+" and isinstance(e1.e2, syntax.ESingleton):
    #     return cond(
    #         bag_contains(e2, e1.e2.e),
    #         bag_subtract(e1.e1, bag_subtract(e2, e1.e2)),
    #         bag_union(bag_subtract(e1.e1, e2), e1.e2.e))
    if isinstance(e2, syntax.ESingleton):
        return syntax.EBinOp(e1, "-", e2).with_type(e1.type)
    # raise NotEfficient(syntax.EBinOp(e1, "-", e2).with_type(e1.type))
    return syntax.EBinOp(e1, "-", e2).with_type(e1.type)

def cond(c, t, e):
    if c == syntax.T:
        return t
    if c == syntax.F:
        return e
    if alpha_equivalent(t, e):
        return t
    return syntax.ECond(c, t, e).with_type(t.type)

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

def checked_bag_delta(e, s):
    tup = bag_delta(e, s)
    return tup
    from cozy.contexts import RootCtx
    n, d = tup
    new_e = mutate(e, s)
    try:
        assert_eq(as_bag(syntax.EBinOp(new_e, "-", e).with_type(e.type)), as_bag(n), context=RootCtx((), ()))
        assert_eq(as_bag(syntax.EBinOp(e, "-", new_e).with_type(e.type)), as_bag(d), context=RootCtx((), ()))
    except:
        print("=" * 20)
        print("exp: {}".format(pprint(e)))
        print("stm:")
        print(pprint(s))
        raise
    return tup

def bag_delta(e, s):
    # print("-" * 20)
    # print("{}.....{}".format(pprint(e), pprint(s)))

    empty = syntax.EEmptyList().with_type(e.type)

    if isinstance(e, target_syntax.EStateVar):
        return checked_bag_delta(e.e, s)

    if isinstance(e, target_syntax.EMap):
        if alpha_equivalent(e.f, mutate(e.f, s)):
            n, d = checked_bag_delta(e.e, s)
            return (
                emap(n, e.f).with_type(e.type),
                emap(d, e.f).with_type(e.type))

    if isinstance(e, target_syntax.EFilter):
        if alpha_equivalent(e.p, mutate(e.p, s)):
            n, d = checked_bag_delta(e.e, s)
            return (
                efilter(n, e.p).with_type(e.type),
                efilter(d, e.p).with_type(e.type))

    if isinstance(e, syntax.EBinOp) and e.op == "+":
        n1, d1 = checked_bag_delta(e.e1, s)
        n2, d2 = checked_bag_delta(e.e2, s)
        return (bag_union(n1, n2), bag_union(d1, d2))

    if isinstance(e, syntax.EVar):
        n = d = syntax.EEmptyList().with_type(e.type)
        for step in flatten(s):
            if isinstance(step, syntax.SCall):
                assert isinstance(step.target, syntax.EVar)
                if step.target == e:
                    if step.func == "add_all":
                        n = bag_union(n, step.args[0])
                    elif step.func == "remove_all":
                        d = bag_union(d, step.args[0])
                    else:
                        raise ValueError(step.func)
            elif isinstance(step, syntax.SAssign) and isinstance(step.lhs, syntax.EVar) and step.lhs != e:
                pass
            else:
                raise NotImplementedError(step)
        from cozy.typecheck import retypecheck, is_collection
        assert retypecheck(n)
        assert retypecheck(d)
        assert is_collection(n.type), pprint(n)
        assert is_collection(d.type), pprint(d)
        return (n, d)

    # raise NotImplementedError(type(e))

    if not isinstance(e, syntax.EVar):
        raise NotImplementedError(e)

    new_e = mutate(e, s)

    try:
        return (
            bag_subtract(new_e, e),
            bag_subtract(e, new_e))
    except NotEfficient as exc:
        print(pprint(e))
        print(pprint(s))
        raise

    if isinstance(s, syntax.SCall) and s.target == e:
        if s.func == "add_all":
            return (s.args[0], empty)
        if s.func == "add":
            return (syntax.ESingleton(s.args[0]).with_type(e.type), empty)
        if s.func == "remove_all":
            return (empty, s.args[0])
        if s.func == "remove":
            return (empty, syntax.ESingleton(s.args[0]).with_type(e.type))
        return (empty, empty)

    if isinstance(s, syntax.SCall) and isinstance(e, syntax.EVar):
        return (empty, empty)

    if isinstance(s, syntax.SSeq):
        while isinstance(s.s1, syntax.SSeq):
            s = syntax.SSeq(s.s1.s1, syntax.SSeq(s.s1.s2, s.s2))
        if isinstance(s.s1, syntax.SDecl):
            n, d = checked_bag_delta(e, s.s2)
            n = subst(n, { s.s1.id : s.s1.val })
            d = subst(d, { s.s1.id : s.s1.val })
            return (n, d)
        n1, d1 = checked_bag_delta(e, s.s1)
        return checked_bag_delta(bag_union(bag_subtract(e, d1), n1), s.s2)
        # n2, d2 = checked_bag_delta(e, s.s2)
        # return (
        #     bag_union(n1, n2),
        #     bag_union(d1, d2))

    if isinstance(s, syntax.SIf):
        nt, dt = checked_bag_delta(e, s.then_branch)
        ne, de = checked_bag_delta(e, s.else_branch)
        return (cond(s.cond, nt, ne), cond(s.cond, dt, de))

    if alpha_equivalent(e, mutate(e, s)):
        return (empty, empty)

    # if isinstance(s, syntax.SAssign):
    #     if alpha_equivalent(e, mutate(e, s)):
    #         return syntax.EEmptyList().with_type(e.type)

    print(pprint(e))
    print(pprint(s))
    raise NotImplementedError()

def new_elems(e, s):
    return bag_delta(e, s)[1]

def del_elems(e, s):
    return bag_delta(e, s)[0]

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
                e = syntax.ELambda(v, e.apply_to(v))
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
        return subst(e, { lval.id : new_value })
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

def minimal_model(formula, collection_depth=4):
    from cozy.solver import satisfy, satisfiable
    if satisfiable(formula, collection_depth=collection_depth):
        print("Minimizing model...")
        from cozy.typecheck import is_collection
        collections = [v for v in free_vars(formula) if is_collection(v.type)]
        for max_len in range(collection_depth * len(collections) + 1):
            model = satisfy(syntax.EAll([
                syntax.ELt(syntax.ESum([syntax.ELen(v) for v in collections]), syntax.ENum(max_len).with_type(syntax.INT)),
                formula]))
            if model is not None:
                return model
    return None

def mutate_in_place(
        lval           : syntax.Exp,
        e              : syntax.Exp,
        op             : syntax.Stm,
        abstract_state : [syntax.EVar],
        assumptions    : [syntax.Exp] = None,
        invariants     : [syntax.Exp] = None,
        subgoals_out   : [syntax.Query] = None):

    if False:
        if assumptions is None:
            assumptions = []

        if subgoals_out is None:
            subgoals_out = []

        parts = []

        for stm in flatten(op):
            parts.extend(break_seq(_mutate_in_place(
                lval, e, stm, abstract_state, assumptions, invariants, subgoals_out)))

        return syntax.seq(parts)

    return _mutate_in_place(
        lval, e, stm, abstract_state, assumptions, invariants, subgoals_out)

def _mutate_in_place(
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
            m.value.apply_to(k),
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
