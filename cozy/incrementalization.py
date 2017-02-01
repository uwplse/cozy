from cozy.common import ADT, declare_case, Visitor, typechecked, fresh_name
from cozy import syntax
from cozy import target_syntax
from cozy.syntax_tools import subst, free_vars, pprint, equal, fresh_var, mk_lambda
from cozy.desugar import desugar_exp

# General deltas
class Delta(ADT): pass
NoDelta           = declare_case(Delta, "NoDelta")
Conditional       = declare_case(Delta, "Conditional",     ["cond", "delta"])
MultiDelta        = declare_case(Delta, "MultiDelta",      ["delta1", "delta2"])
ForEachDelta      = declare_case(Delta, "ForEachDelta",    ["elems", "x", "delta"])
Become            = declare_case(Delta, "Become", ["e"])

# Bags
BagAdd            = declare_case(Delta, "BagAdd",          ["e"])
BagAddAll         = declare_case(Delta, "BagAddAll",       ["e"])
BagRemove         = declare_case(Delta, "BagRemove",       ["e"])
BagRemoveAll      = declare_case(Delta, "BagRemoveAll",    ["e"])
BagElemUpdated    = declare_case(Delta, "BagElemUpdated",  ["elem", "delta"])

# Numbers
AddNum            = declare_case(Delta, "AddNum", ["e"])

# Maps
MapUpdate         = declare_case(Delta, "MapUpdate", ["key", "delta"])

# Records
RecordFieldUpdate = declare_case(Delta, "RecordFieldUpdate", ["f", "delta"])

# Tuples
TupleEntryUpdate  = declare_case(Delta, "TupleEntryUpdate", ["n", "delta"])

def fmap(f, delta):
    if isinstance(delta, NoDelta):
        return delta
    elif isinstance(delta, Conditional):
        return Conditional(f(delta.cond), fmap(f, delta.delta))
    elif isinstance(delta, MultiDelta):
        return MultiDelta(fmap(f, delta.delta1), fmap(f, delta.delta2))
    elif isinstance(delta, ForEachDelta):
        return ForEachDelta(f(elems), delta.x, fmap(f, delta.delta))
    elif isinstance(delta, Become):
        return Become(f(delta.e))
    elif isinstance(delta, BagAdd):
        return BagAdd(f(delta.e))
    elif isinstance(delta, BagAddAll):
        return BagAddAll(f(delta.e))
    elif isinstance(delta, BagRemove):
        return BagRemove(f(delta.e))
    elif isinstance(delta, BagRemoveAll):
        return BagRemoveAll(f(delta.e))
    elif isinstance(delta, AddNum):
        return AddNum(f(delta.e))
    elif isinstance(delta, BagElemUpdated):
        return BagElemUpdated(delta.elem, fmap(f, delta.delta))
    elif isinstance(delta, RecordFieldUpdate):
        return RecordFieldUpdate(delta.f, fmap(f, delta.delta))
    else:
        raise NotImplementedError(delta)

def multi_delta(deltas):
    deltas = [d for d in deltas if not isinstance(d, NoDelta)]
    if len(deltas) == 0:
        return NoDelta()
    d = deltas[0]
    for i in range(1, len(deltas)):
        d = MultiDelta(d, deltas[i])
    return d

def mk_TupleEntryUpdate(n, delta):
    if isinstance(delta, NoDelta):
        return delta
    return TupleEntryUpdate(n, delta)

def rewrite_becomes(delta, f):
    class V(Visitor):
        def visit_Become(self, d):
            return Become(f(d.e))
        def visit_Delta(self, d):
            return d
    return map_cond(delta, V().visit)

def mk_conditional(cond, delta):
    # if isinstance(delta, NoDelta):
    #     return delta
    return Conditional(cond, delta)

def map_cond(delta, f):
    class V(Visitor):
        def visit_Conditional(self, d):
            return mk_conditional(d.cond, self.visit(d.delta))
        def visit_MultiDelta(self, d):
            return multi_delta([
                self.visit(d.delta1),
                self.visit(d.delta2)])
        def visit_Delta(self, d):
            return f(d)
    return V().visit(delta)

def _push_delta_through_field_access(members : { str : syntax.Type }, lhs, delta):
    if isinstance(lhs, syntax.EVar):
        if isinstance(lhs.type, syntax.THandle):
            bags = [ m for (m, ty) in members.items() if type(ty) in (syntax.TSet, syntax.TBag) and ty.t == lhs.type ]
            if len(bags) == 0:
                return (lhs, NoDelta())
            if len(bags) != 1:
                raise NotImplementedError("TODO: handle the case where >1 members change in response to op")
            bag_id = bags[0]
            bag = syntax.EVar(bag_id).with_type(members[bag_id])
            return (bag, BagElemUpdated(lhs, delta))
        elif isinstance(lhs, syntax.EVar) and lhs.id in members:
            return (lhs, delta)
    elif isinstance(lhs, syntax.EGetField):
        return _push_delta_through_field_access(members, lhs.e, RecordFieldUpdate(lhs.f, delta))
    raise Exception("not sure how to incrementalize change to {}".format(pprint(lhs)))

@typechecked
def to_delta(members : [(str, syntax.Type)], op : syntax.Op) -> (syntax.Exp, Delta):
    """
    Input: synax.Op
    Output: (member, delta) indicating that op transforms member by delta
    """
    name = op.name
    args = op.args
    members = dict(members)
    if isinstance(op.body, syntax.SCall):
        target = op.body.target
        if   op.body.func == "add":        delta = BagAdd(op.body.args[0])
        elif op.body.func == "remove":     delta = BagRemove(op.body.args[0])
        elif op.body.func == "remove_all": delta = BagRemoveAll(op.body.args[0])
        elif op.body.func == "addFront":   delta = ListAddFront(op.body.args[0])
        elif op.body.func == "addBack":    delta = ListAddBack(op.body.args[0])
        else: raise Exception("Unknown func: {}".format(op.body.func))
    elif isinstance(op.body, syntax.SAssign):
        target = op.body.lhs
        delta = Become(op.body.rhs)
    else:
        raise NotImplementedError(str(op.body))
    member, new_delta = _push_delta_through_field_access(members, target, delta)
    return (member, new_delta)

@typechecked
def derivative(
        e     : syntax.Exp,
        var   : syntax.EVar,
        delta : Delta,
        ctx   : [syntax.EVar]) -> (Delta, [syntax.Query]):
    """
    How does `e` change when `var` changes by `delta`?
    The answer may require some additional sub-queries to implement.
    If subqueries are generated, vars in `ctx` are assumed to be part
    of the data structure state.
    """

    if var not in free_vars(e):
        return (NoDelta(), [])

    if e == var:
        return (delta, [])

    subgoals = []

    def make_subgoal(e, assumptions=None):
        if assumptions is None:
            assumptions = []
        fvs = free_vars(e)
        if not any(v in ctx for v in fvs):
            return e
        e = desugar_exp(e)
        query_name = fresh_name()
        query_vars = [v for v in fvs if v not in ctx]
        query = syntax.Query(query_name, [(arg.id, arg.type) for arg in query_vars], assumptions, e)
        subgoals.append(query)
        return syntax.ECall(query_name, query_vars).with_type(e.type)

    def recurse(*args, **kwargs):
        (res, sgs) = derivative(*args, **kwargs)
        subgoals.extend(sgs)
        return res

    e_post_delta = subst(e, { var.id : apply_delta(var, delta) })
    if e.type == syntax.INT:
        change = AddNum(make_subgoal(syntax.EBinOp(e_post_delta, "-", e).with_type(syntax.INT)))
    elif isinstance(e.type, syntax.TBag):
        change = multi_delta([
            BagAddAll   (make_subgoal(target_syntax.EFilter(e_post_delta, mk_lambda(e.type.t, lambda x: syntax.ENot(syntax.EBinOp(x, "in", e).with_type(syntax.BOOL)))).with_type(e.type))),
            BagRemoveAll(make_subgoal(target_syntax.EFilter(e, mk_lambda(e.type.t, lambda x: syntax.ENot(syntax.EBinOp(x, "in", e_post_delta).with_type(syntax.BOOL)))).with_type(e.type)))])
    elif isinstance(e.type, syntax.TTuple):
        deltas = []
        for i in range(len(e.type.ts)):
            d = recurse(syntax.ETupleGet(e, i).with_type(e.type.ts[i]), var, delta, ctx)
            if not isinstance(d, NoDelta):
                deltas.append(TupleEntryUpdate(i, d))
        change = multi_delta(deltas)
    elif isinstance(e.type, syntax.TBool):
        change = Become(make_subgoal(e_post_delta))
    # elif isinstance(e.type, syntax.TMap):
        # TODO:
        #    altered_keys = make_subgoal(keys_that_changed)
        #    value_delta    = derivative(my_value_func, ...)
        #    return ForEachDelta(altered_keys, value_delta)
    else:
        raise NotImplementedError("{} of type {}".format(pprint(e), e.type))

    return (change, subgoals)

@typechecked
def apply_delta(
        x      : syntax.Exp,
        delta  : Delta) -> syntax.Exp:
    """
    Apply the given change to the given expression.
    """

    class V(Visitor):
        def visit_NoDelta(self, delta):
            return x
        def visit_Become(self, delta):
            return delta.e
        def visit_AddNum(self, delta):
            return syntax.EBinOp(x, "+", delta.e).with_type(x.type)
        def visit_BagAdd(self, delta):
            return syntax.EBinOp(x, "+", syntax.ESingleton(delta.e).with_type(x.type)).with_type(x.type)
        def visit_BagAddAll(self, delta):
            return syntax.EBinOp(x, "+", delta.e).with_type(x.type)
        def visit_BagRemove(self, delta):
            return target_syntax.EFilter(x, mk_lambda(x.type.t, lambda elem: syntax.ENot(equal(elem, delta.e))))
        def visit_BagRemoveAll(self, delta):
            return target_syntax.EFilter(x, mk_lambda(x.type.t, lambda elem: syntax.ENot(syntax.EBinOp(elem, "in", delta.e).with_type(syntax.BOOL))))
        def visit_Conditional(self, delta):
            return syntax.ECond(delta.cond, self.visit(delta.delta), x).with_type(x.type)
        def visit_MultiDelta(self, delta):
            return apply_delta(apply_delta(x, delta.delta1), delta.delta2)
        def visit_TupleEntryUpdate(self, delta):
            if isinstance(x, syntax.ETuple):
                return syntax.ETuple(tuple(
                    apply_delta(x.es[i], delta.delta) if i == delta.n else x.es[i]
                    for i in range(len(x.es)))).with_type(x.type)
            else:
                raise NotImplementedError(x)
        def visit_Delta(self, d):
            raise NotImplementedError("apply {} to {}".format(d, x))

    return V().visit(delta)

@typechecked
def apply_delta_in_place(
        x      : syntax.Exp,
        delta  : Delta) -> syntax.Stm:
    """
    Apply the given change in-place to the given L-value.
    """

    class V(Visitor):
        def visit_NoDelta(self, delta):
            return syntax.SNoOp()
        def visit_Become(self, delta):
            return syntax.SAssign(x, delta.e)
        def visit_BagAdd(self, delta):
            return syntax.SCall(x, "add", [delta.e])
        def visit_BagAddAll(self, delta):
            elem = fresh_var(x.type.t)
            return target_syntax.SForEach(elem, delta.e, apply_delta_in_place(x, BagAdd(elem)))
        def visit_BagRemove(self, delta):
            return syntax.SCall(x, "remove", [delta.e])
        def visit_BagRemoveAll(self, delta):
            elem = fresh_var(x.type.t)
            return target_syntax.SForEach(elem, delta.e, apply_delta_in_place(x, BagRemove(elem)))
        def visit_BagElemUpdated(self, delta):
            return syntax.SNoOp()
        def visit_ForEachDelta(self, delta):
            return target_syntax.SForEach(delta.x, delta.elems, self.visit(delta.delta))
        def visit_MapUpdate(self, delta):
            v = fresh_var(x.type.v)
            return target_syntax.SMapUpdate(x, delta.key, v, apply_delta_in_place(v, delta.delta))
        def visit_AddNum(self, delta):
            return syntax.SAssign(x, syntax.EBinOp(x, "+", delta.e))
        def visit_Conditional(self, delta):
            substm = self.visit(delta.delta)
            return syntax.SIf(delta.cond, substm, syntax.SNoOp())
        def visit_RecordFieldUpdate(self, delta):
            if not (isinstance(x.type, syntax.TRecord) or isinstance(x.type, syntax.THandle)):
                raise Exception("ill-typed expression for update: " + repr(x) + " [type={}]".format(repr(x.type)))
            field_type = dict(x.type.fields)[delta.f] if isinstance(x.type, syntax.TRecord) else x.type.value_type
            return apply_delta_in_place(syntax.EGetField(x, delta.f).with_type(field_type), delta.delta)
        def visit_TupleEntryUpdate(self, delta):
            elem_type = x.type.ts[delta.n]
            return apply_delta_in_place(syntax.ETupleGet(x, delta.n).with_type(elem_type), delta.delta)
        def visit_MultiDelta(self, delta):
            return syntax.SSeq(
                self.visit(delta.delta1),
                self.visit(delta.delta2))
        def visit_Delta(self, d):
            raise NotImplementedError(str(d))

    return V().visit(delta)
