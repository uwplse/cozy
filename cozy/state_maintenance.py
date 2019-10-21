"""Functions for managing stateful computation.

Important functions:
 - mutate: compute the new value of an expression after a statement executes
 - mutate_in_place: write code to keep a derived value in sync with its inputs
"""

import itertools

from cozy.common import fresh_name
from cozy import syntax
from cozy import target_syntax
from cozy.syntax_tools import free_vars, pprint, fresh_var, strip_EStateVar, lightweight_subst, BottomUpRewriter, alpha_equivalent
from cozy.typecheck import is_numeric
from cozy.solver import valid
from cozy.opts import Option
from cozy.structures import extension_handler
from cozy.evaluation import construct_value

skip_stateless_synthesis = Option("skip-stateless-synthesis", bool, False,
    description="Do not waste time optimizing expressions that do not depend on the data structure state")
update_numbers_with_deltas = Option("update-numbers-with-deltas", bool, False)

def mutate(e : syntax.Exp, op : syntax.Stm) -> syntax.Exp:
    """Return the new value of `e` after executing `op`.

    Evaluating the returned expression will give the same output as running
    `op` followed by evaluating the input expression `e`.
    """
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
            e2 = lightweight_subst(e2, op.s1.var, op.s1.val)
        return e2
    elif isinstance(op, syntax.SDecl):
        return e
    else:
        raise NotImplementedError(type(op))

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
            res = syntax.EGetField(ee, e.field_name).with_type(e.type)
            if e.e.type == t and e.field_name == "val":
                res = syntax.ECond(syntax.EEq(ee, ptr), new_value, res).with_type(e.type)
            return res
    return V().visit(e)

def _do_assignment(lval : syntax.Exp, new_value : syntax.Exp, e : syntax.Exp) -> syntax.Exp:
    """
    Return the value of `e` after the assignment `lval = new_value`.
    """
    if isinstance(lval, syntax.EVar):
        return lightweight_subst(e, lval, new_value)
    elif isinstance(lval, syntax.EGetField):
        if isinstance(lval.e.type, syntax.THandle):
            assert lval.field_name == "val"
            # Because any two handles might alias, we need to rewrite all
            # reachable handles in `e`.
            return replace_get_value(e, lval.e, new_value)
        return _do_assignment(lval.e, _replace_field(lval.e, lval.field_name, new_value), e)
    else:
        raise Exception("not an lvalue: {}".format(pprint(lval)))

def _replace_field(record : syntax.Exp, field : str, new_value : syntax.Exp) -> syntax.Exp:
    return syntax.EMakeRecord(tuple(
        (f, new_value if f == field else syntax.EGetField(record, f).with_type(ft))
        for f, ft in record.type.fields)).with_type(record.type)

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

    Parameters:
      - abstract_state: variables that are part of the abstract state of the
        data structure
      - assumptions: formulas that are known to be true before `op` runs
      - invariants: true formulas about the abstract state
      - subgoals_out [out parameter]: a list that will be filled with new
        query operations

    The queries written into `subgoals_out` will be used by the returned code.
    They will include `assumptions` as preconditions, but not `invariants`.
    This behavior allows them to be added to an implementation that already has
    the given invariants.

    Note that the returned subgoals are all in terms of the pre-state before
    `op` runs.
    """

    if assumptions is None:
        assumptions = []
    else:
        assumptions = list(assumptions)

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
        ret = h.mutate_in_place(
            lval=lval,
            e=e,
            op=op,
            assumptions=assumptions,
            invariants=invariants,
            make_subgoal=make_subgoal)
        if ret is not None:
            return ret

    # fallback: use an update sketch
    new_e = mutate(e, op)
    s, sgs = sketch_update(lval, e, new_e, ctx=abstract_state, assumptions=assumptions, invariants=invariants)
    subgoals_out.extend(sgs)
    return s

def value_at(m, k):
    """Make an AST node for m[k]."""
    if isinstance(m, target_syntax.EMakeMap2):
        return syntax.ECond(
            syntax.EIn(k, m.e),
            m.value_function.apply_to(k),
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

    if alpha_equivalent(old_value, new_value):
        return (syntax.SNoOp(), [])
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
        v = fresh_var(t.elem_type)
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
