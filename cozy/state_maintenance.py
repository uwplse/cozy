from cozy.common import fresh_name, identity_func
from cozy import syntax
from cozy import target_syntax
from cozy.syntax_tools import free_vars, pprint, fresh_var, mk_lambda, alpha_equivalent, strip_EStateVar, subst, break_seq, BottomUpRewriter
from cozy.typecheck import is_numeric
from cozy.solver import valid
from cozy.opts import Option
from cozy.structures import extension_handler

skip_stateless_synthesis = Option("skip-stateless-synthesis", bool, False,
    description="Do not waste time optimizing expressions that do not depend on the data structure state")
update_numbers_with_deltas = Option("update-numbers-with-deltas", bool, True)

def mutate(e : syntax.Exp, op : syntax.Stm, k=identity_func) -> syntax.Exp:
    """
    Return the new value of `e` after executing `op`.
    """
    if isinstance(op, syntax.SNoOp):
        return k(e)
    elif isinstance(op, syntax.SAssign):
        return k(_do_assignment(op.lhs, op.rhs, e))
    elif isinstance(op, syntax.SCall):
        if op.func == "add":
            return mutate(e, syntax.SCall(op.target, "add_all", (syntax.ESingleton(op.args[0]).with_type(op.target.type),)), k=k)
        # TODO: list functions
        # elif op.func == "add_back":
        #     pass
        # elif op.func == "add_front":
        #     pass
        # elif op.func == "remove_back":
        #     pass
        # elif op.func == "remove_front":
        #     pass
        elif op.func == "add_all":
            return mutate(e, syntax.SAssign(op.target, syntax.EBinOp(op.target, "+", op.args[0]).with_type(op.target.type)), k=k)
        elif op.func == "remove":
            return mutate(e, syntax.SCall(op.target, "remove_all", (syntax.ESingleton(op.args[0]).with_type(op.target.type),)), k=k)
        elif op.func == "remove_all":
            return mutate(e, syntax.SAssign(op.target, syntax.EBinOp(op.target, "-", op.args[0]).with_type(op.target.type)), k=k)
        else:
            raise Exception("Unknown func: {}".format(op.func))
    elif isinstance(op, syntax.SIf):
        return k(ECond(op.cond,
            mutate(e, op.then_branch),
            mutate(e, op.else_branch)).with_type(e.type))
    elif isinstance(op, syntax.SSeq):
        return mutate(e, op.s2, k=lambda e: mutate(e, op.s1, k=k))
    elif isinstance(op, syntax.SDecl):
        # TODO: this doesn't work if op.id is in free_vars(k)...
        return subst(k(e), { op.id : op.val })
    else:
        raise NotImplementedError(type(op))

def replace_get_value(e : syntax.Exp, t : syntax.THandle, f):
    class V(BottomUpRewriter):
        def visit_EGetField(self, e):
            ee = self.visit(e.e)
            res = syntax.EGetField(ee, e.f).with_type(e.type)
            if e.e.type == t and e.f == "val":
                return f(res)
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
            # Because any two handles might alias, we need to rewrite all
            # reachable handles in `e`.
            return global_rewrite(e, lval.e.type, lambda h: syntax.ECond(syntax.EEq(h, lval.e), target_syntax.EWithAlteredValue(h, new_value).with_type(h.type), h).with_type(h.type))
        return _do_assignment(lval.e, _replace_field(lval.e, lval.f, new_value), e)
    else:
        raise Exception("not an lvalue: {}".format(pprint(lval)))

def _fix_map(m : target_syntax.EMap) -> syntax.Exp:
    return m
    from cozy.simplification import simplify
    m = simplify(m)
    if not isinstance(m, target_syntax.EMap):
        return m
    # print("fixing {}...".format(pprint(m)))
    elem_type = m.e.type.t
    assert m.f.body.type == elem_type
    changed = target_syntax.EFilter(m.e, mk_lambda(elem_type, lambda x: syntax.ENot(syntax.EBinOp(x, "===", m.f.apply_to(x)).with_type(syntax.BOOL)))).with_type(m.e.type)
    e = syntax.EBinOp(syntax.EBinOp(m.e, "-", changed).with_type(m.e.type), "+", target_syntax.EMap(changed, m.f).with_type(m.e.type)).with_type(m.e.type)
    if not valid(syntax.EEq(m, e)):
        print("WARNING: rewrite failed")
        print("_fix_map({!r})".format(m))
        return m
    # print("Fix: {} ----> {}".format(pprint(m), pprint(e)))
    return e

def _replace_field(record : syntax.Exp, field : str, new_value : syntax.Exp) -> syntax.Exp:
    return syntax.EMakeRecord(tuple(
        (f, new_value if f == field else syntax.EGetField(record, f).with_type(ft))
        for f, ft in record.type.fields)).with_type(record.type)

def global_rewrite(e : syntax.Exp, t : syntax.Type, change) -> syntax.Exp:
    """
    Apply `change` to all reachable values of type `t` in `e`.
    """
    fvs = free_vars(e)
    return subst(e, { v.id : _global_rewrite(v, t, change) for v in fvs })

def _global_rewrite(e : syntax.Exp, t : syntax.Type, change) -> syntax.Exp:
    if e.type == t:
        return change(e)

    if isinstance(e.type, syntax.TBag) or isinstance(e.type, syntax.TList):
        return _fix_map(target_syntax.EMap(e, mk_lambda(e.type.t, lambda x: _global_rewrite(x, t, change))).with_type(e.type))
    elif isinstance(e.type, syntax.THandle):
        old_val = syntax.EGetField(e, "val").with_type(e.type.value_type)
        new_val = _global_rewrite(old_val, t, change)
        if old_val == new_val:
            return e
        return target_syntax.EWithAlteredValue(e, new_val).with_type(e.type)
    elif isinstance(e.type, syntax.TTuple):
        return syntax.ETuple(tuple(_global_rewrite(syntax.ETupleGet(e, i).with_type(e.type.ts[i]), t, change) for i in range(len(e.type.ts)))).with_type(e.type)
    elif isinstance(e.type, syntax.TRecord):
        return syntax.EMakeRecord(tuple(
            (f, _global_rewrite(syntax.EGetField(e, f).with_type(ft), t, change)) for f, ft in e.type.fields)).with_type(e.type)
    elif e.type == syntax.INT or e.type == syntax.LONG or e.type == syntax.BOOL or e.type == syntax.STRING or isinstance(e.type, syntax.TNative) or isinstance(e.type, syntax.TEnum):
        return e
    else:
        raise NotImplementedError(repr(e.type))

def mutate_in_place(
        lval           : syntax.Exp,
        e              : syntax.Exp,
        op             : syntax.Stm,
        abstract_state : [syntax.EVar],
        assumptions    : [syntax.Exp] = None,
        subgoals_out   : [syntax.Query] = None) -> syntax.Stm:
    """
    Produce code to update `lval` that tracks derived value `e` when `op` is
    run.
    """

    if assumptions is None:
        assumptions = []

    if subgoals_out is None:
        subgoals_out = []

    def make_subgoal(e, a=[], docstring=None):
        # e = strip_EStateVar(e)
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
            make_subgoal=make_subgoal)

    # TODO!
    # from cozy.syntax import EImplies, EAll, EEq, ELe, EGe, EArgMin, EArgMax, ENot, ELambda, seq, ELen, SCall, SAssign, SForEach, INT, EBinOp, ESingleton
    # from cozy.target_syntax import EDeepIn, EDeepEq, EFilter, EStateVar
    # from cozy.structures.heaps import to_heap, EHeapPeek2
    # if False and (isinstance(e, EArgMin) or isinstance(e, EArgMax)):
    #     new_elems = mutate(e.e, op)
    #     if valid(EImplies(EAll(assumptions), EEq(e.e, new_elems))):
    #         # Elements don't change!
    #         h= to_heap(e)
    #         h = EStateVar(h).with_type(h.type)
    #         # if min changed: use heap
    #         old_best = e.f.apply_to(e)
    #         compare = ELe if isinstance(e, EArgMin) else EGe
    #         new_best = mutate(old_best, op)
    #         cond = compare(new_best, EStateVar(old_best).with_type(old_best.type))
    #         return syntax.SIf(
    #             make_subgoal(cond),
    #             syntax.SAssign(lval, make_subgoal(
    #                 type(e)(EBinOp(
    #                     ESingleton(EStateVar(e).with_type(e.type)).with_type(e.e.type), "+",
    #                     ESingleton(mutate(e, op)).with_type(e.e.type)).with_type(e.e.type), e.f).with_type(e.type), a=[cond])),
    #             syntax.SAssign(lval, make_subgoal(
    #                 EHeapPeek2(h,
    #                 EStateVar(ELen(e.e)).with_type(INT)).with_type(lval.type), a=[ENot(cond)])))
    #         # return syntax.SAssign(lval, EHeapPeek(
    #         #     make_subgoal(EStateVar(h).with_type(h.type)),
    #         #     make_subgoal(EStateVar(ELen(e.e)).with_type(INT))).with_type(h.type))

    # fallback: use an update sketch
    new_e = mutate(e, op)
    s, sgs = sketch_update(lval, e, new_e, ctx=abstract_state, assumptions=assumptions)
    subgoals_out.extend(sgs)
    return s

def value_at(m, k):
    """
    Assuming k is in EMapKeys(m), produce the value at k.
    """
    if isinstance(m, target_syntax.EMakeMap2):
        return m.value.apply_to(k)
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
        assumptions : [syntax.Exp] = []) -> (syntax.Stm, [syntax.Query]):
    """
    Write code to update `lval` when it changes from `old_value` to `new_value`.
    Variables in `ctx` are assumed to be part of the data structure abstract
    state, and `assumptions` will be appended to all generated subgoals.

    This function returns a statement (code to update `lval`) and a list of
    subgoals (new queries that appear in the code).
    """

    if valid(syntax.EImplies(syntax.EAll(assumptions), syntax.EEq(old_value, new_value))):
        return (syntax.SNoOp(), [])

    subgoals = []
    new_value = strip_EStateVar(new_value)

    def make_subgoal(e, a=[], docstring=None):
        # e = strip_EStateVar(e)
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
    # elif isinstance(t, syntax.TList):
    #     raise NotImplementedError()
    elif is_numeric(t) and update_numbers_with_deltas.value:
        change = make_subgoal(syntax.EBinOp(new_value, "-", old_value).with_type(t), docstring="delta for {}".format(pprint(lval)))
        stm = syntax.SAssign(lval, syntax.EBinOp(lval, "+", change).with_type(t))
    elif isinstance(t, syntax.TTuple):
        get = lambda val, i: syntax.ETupleGet(val, i).with_type(t.ts[i])
        stm = syntax.seq([
            recurse(get(lval, i), get(old_value, i), get(new_value, i), ctx, assumptions)
            for i in range(len(t.ts))])
    elif isinstance(t, syntax.TRecord):
        get = lambda val, i: syntax.EGetField(val, t.fields[i][0]).with_type(t.fields[i][1])
        stm = syntax.seq([
            recurse(get(lval, i), get(old_value, i), get(new_value, i), ctx, assumptions)
            for i in range(len(t.fields))])
    elif isinstance(t, syntax.TMap):
        k = fresh_var(lval.type.k)
        v = fresh_var(lval.type.v)
        key_bag = syntax.TBag(lval.type.k)

        if True:

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
                assumptions = assumptions + [syntax.EIn(k, new_or_modified), syntax.EImplies(syntax.EIn(k, old_keys), syntax.EEq(v, value_at(old_value, k)))])
            s2 = syntax.SForEach(k, make_subgoal(new_or_modified, docstring="new or modified keys from {}".format(pprint(lval))),
                target_syntax.SMapUpdate(lval, k, v, update_value))

            stm = syntax.SSeq(s1, s2)
        elif True:
            old_keys = target_syntax.EMapKeys(old_value).with_type(key_bag)
            new_keys = target_syntax.EMapKeys(new_value).with_type(key_bag)

            # (1) exit set
            deleted_keys = syntax.EBinOp(old_keys, "-", new_keys).with_type(key_bag)
            s1 = syntax.SForEach(k, make_subgoal(deleted_keys, docstring="keys removed from {}".format(pprint(lval))),
                target_syntax.SMapDel(lval, k))

            # (2) modify set
            common_keys = target_syntax.EFilter(old_keys, target_syntax.ELambda(k, syntax.EIn(k, new_keys))).with_type(key_bag)
            update_value = recurse(
                v,
                value_at(old_value, k),
                value_at(new_value, k),
                ctx = ctx,
                assumptions = assumptions + [syntax.EIn(k, common_keys), syntax.ENot(syntax.EEq(value_at(old_value, k), value_at(new_value, k)))])
            if isinstance(update_value, syntax.SNoOp):
                s2 = update_value
            else:
                altered_keys = target_syntax.EFilter(
                    common_keys,
                    target_syntax.ELambda(k,
                        syntax.ENot(syntax.EEq(value_at(old_value, k), value_at(new_value, k))))).with_type(key_bag)
                s2 = syntax.SForEach(k, make_subgoal(altered_keys, docstring="altered keys in {}".format(pprint(lval))),
                    target_syntax.SMapUpdate(lval, k, v, update_value))

            # (3) enter set
            fresh_keys = syntax.EBinOp(new_keys, "-", old_keys).with_type(key_bag)
            s3 = syntax.SForEach(k, make_subgoal(fresh_keys, docstring="new keys in {}".format(pprint(lval))),
                target_syntax.SMapPut(lval, k, make_subgoal(value_at(new_value, k), a=[syntax.EIn(k, fresh_keys)], docstring="new value inserted at {}".format(pprint(target_syntax.EMapGet(lval, k))))))

            stm = syntax.seq([s1, s2, s3])

        else:
            # update_value = code to update for value v at key k (given that k is an altered key)
            update_value = recurse(
                v,
                value_at(old_value, k),
                value_at(new_value, k),
                ctx = ctx,
                assumptions = assumptions + [syntax.ENot(syntax.EEq(value_at(old_value, k), value_at(new_value, k)))])

            # altered_keys = [k | k <- distinct(lval.keys() + new_value.keys()), value_at(old_value, k) != value_at(new_value, k))]
            altered_keys = make_subgoal(
                target_syntax.EFilter(
                    syntax.EUnaryOp(syntax.UOp.Distinct, syntax.EBinOp(
                        target_syntax.EMapKeys(old_value).with_type(key_bag), "+",
                        target_syntax.EMapKeys(new_value).with_type(key_bag)).with_type(key_bag)).with_type(key_bag),
                    target_syntax.ELambda(k,
                        syntax.ENot(syntax.EEq(value_at(old_value, k), value_at(new_value, k))))
                ).with_type(key_bag))
            stm = syntax.SForEach(k, altered_keys,
                target_syntax.SMapUpdate(lval, k, v, update_value))
    else:
        # Fallback rule: just compute a new value from scratch
        stm = syntax.SAssign(lval, make_subgoal(new_value, docstring="new value for {}".format(pprint(lval))))

    return (stm, subgoals)
