from cozy.common import fresh_name
from cozy import syntax
from cozy import target_syntax
from cozy.syntax_tools import free_vars, pprint, fresh_var, mk_lambda, alpha_equivalent
from cozy.desugar import desugar_exp
from cozy.typecheck import is_numeric

def delta_form(members : [(str, syntax.Type)], op : syntax.Op) -> { str : syntax.Exp }:
    """
    Given the abstract state of a data structure and an imperative operation
    that modifies it, return new values for the abstract state in terms of the
    old values.

    Input:
        members - a list of (id, type) tuples specifying the abstract state
        op      - an imperative operation

    Output:
        dictionary mapping id->new_exp (suitable for use by syntax_tools.subst)
    """
    res = { v : syntax.EVar(v).with_type(t) for (v, t) in members }
    return _delta_form(res, op.body)

def _delta_form(res : { str : syntax.Exp }, op : syntax.Stm) -> { str : syntax.Exp }:
    if isinstance(op, syntax.SNoOp):
        pass
    elif isinstance(op, syntax.SCall):
        update = _rewriter(op.target)
        if op.func == "add":
            update(res, lambda old: syntax.EBinOp(old, "+", syntax.ESingleton(op.args[0]).with_type(old.type)).with_type(old.type))
        elif op.func == "remove":
            update(res, lambda old: syntax.EBinOp(old, "-", syntax.ESingleton(op.args[0]).with_type(old.type)).with_type(old.type))
        else:
            raise Exception("Unknown func: {}".format(op.func))
    elif isinstance(op, syntax.SAssign):
        update = _rewriter(op.lhs)
        update(res, lambda old: op.rhs)
    else:
        raise NotImplementedError(type(op.body))

    return res

def _update_handle(e : syntax.Exp, handle : syntax.EVar, change):
    if isinstance(e.type, syntax.TBag):
        return target_syntax.EMap(e, mk_lambda(e.type.t, lambda x: _update_handle(x, handle, change))).with_type(e.type)
    elif isinstance(e.type, syntax.THandle):
        if e.type == handle.type:
            return syntax.ECond(syntax.EEq(e, handle), change(e), e).with_type(e.type)
        else:
            return e
    elif isinstance(e.type, syntax.TTuple):
        return syntax.ETuple(tuple(_update_handle(syntax.ETupleGet(e, i).with_type(e.type.ts[i]), handle, change) for i in range(len(e.type.ts)))).with_type(e.type)
    elif e.type == syntax.INT or e.type == syntax.LONG or e.type == syntax.BOOL or e.type == syntax.STRING or isinstance(e.type, syntax.TNative) or isinstance(e.type, syntax.TEnum):
        return e
    else:
        raise NotImplementedError(repr(e.type))

def _rewriter(lval : syntax.Exp):
    if isinstance(lval, syntax.EVar):
        def f(env, change):
            if isinstance(lval.type, syntax.THandle):
                new_values = {id : _update_handle(e, lval, change) for (id, e) in env.items()}
                for id in env.keys():
                    env[id] = new_values[id]
            elif lval.id in env:
                env[lval.id] = change(env[lval.id])
    elif isinstance(lval, syntax.EGetField):
        g = _rewriter(lval.e)
        def f(env, change):
            if isinstance(lval.e.type, syntax.THandle):
                g(env, lambda old: target_syntax.EWithAlteredValue(old, change(syntax.EGetField(old, "val").with_type(lval.e.type.value_type))).with_type(old.type))
            else:
                g(env, lambda old: syntax.EMakeRecord(tuple(((f, syntax.EGetField(old, f).with_type(t)) if f != lval.f else (f, change(syntax.EGetField(old, f)))) for (f, t) in lval.e.type.fields)).with_type(old.type))
    else:
        raise Exception("not an lvalue: {}".format(pprint(lval)))
    return f

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

    if alpha_equivalent(old_value, new_value):
        return (syntax.SNoOp(), [])

    subgoals = []

    def make_subgoal(e, a=[]):
        e = desugar_exp(e)
        if not any(v in ctx for v in free_vars(e)):
            return e
        query_name = fresh_name("query")
        query = syntax.Query(query_name, syntax.Visibility.Internal, [], assumptions + a, e)
        query_vars = [v for v in free_vars(query) if v not in ctx]
        query.args = [(arg.id, arg.type) for arg in query_vars]
        subgoals.append(query)
        return syntax.ECall(query_name, query_vars).with_type(e.type)

    def recurse(*args, **kwargs):
        (code, sgs) = sketch_update(*args, **kwargs)
        subgoals.extend(sgs)
        return code

    t = lval.type
    if isinstance(t, syntax.TBag):
        to_add = make_subgoal(syntax.EBinOp(new_value, "-", old_value).with_type(t))
        to_del = make_subgoal(syntax.EBinOp(old_value, "-", new_value).with_type(t))
        v = fresh_var(t.t)
        stm = syntax.seq([
            syntax.SForEach(v, to_del, syntax.SCall(lval, "remove", [v])),
            syntax.SForEach(v, to_add, syntax.SCall(lval, "add", [v]))])
    elif is_numeric(t):
        change = make_subgoal(syntax.EBinOp(new_value, "-", old_value).with_type(t))
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
    elif isinstance(t, syntax.THandle):
        get_val = lambda val: syntax.EGetField(val, "val").with_type(t.value_type)
        stm = recurse(get_val(lval), get_val(old_value), get_val(new_value), ctx, assumptions)
    elif isinstance(t, syntax.TMap):
        value_at = lambda m, k: target_syntax.EMapGet(m, k).with_type(lval.type.v)

        k = fresh_var(lval.type.k)
        v = fresh_var(lval.type.v)
        key_bag = syntax.TBag(lval.type.k)

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
        stm = syntax.SAssign(lval, make_subgoal(new_value))

    return (stm, subgoals)
