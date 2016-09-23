from common import ADT, declare_case, Visitor, typechecked, fresh_name
import syntax
from syntax_tools import subst, free_vars

class Delta(ADT): pass
NoDelta           = declare_case(Delta, "NoDelta")
BagAdd            = declare_case(Delta, "BagAdd",          ["e"])
BagRemove         = declare_case(Delta, "BagRemove",       ["e"])
Conditional       = declare_case(Delta, "Conditional",     ["cond", "delta"])
MultiDelta        = declare_case(Delta, "MultiDelta",      ["delta1", "delta2"])
AddNum            = declare_case(Delta, "AddNum", ["e"])
MapUpdate         = declare_case(Delta, "MapUpdate", ["key", "delta"])
RecordFieldUpdate = declare_case(Delta, "RecordFieldUpdate", ["f", "delta"])

def multi_delta(deltas):
    if not isinstance(deltas, list):
        deltas = list(deltas)
    if len(deltas) == 0:
        return NoDelta()
    d = deltas[0]
    for i in range(1, len(deltas)):
        d = MultiDelta(d, deltas[i])
    return d

@typechecked
def to_delta(op : syntax.Op) -> (syntax.Exp, Delta):
    """
    Input: synax.Op
    Output: (member, delta) indicating that op transforms member by delta
    """
    name = op.name
    args = op.args
    if isinstance(op.body, syntax.SCall):
        member = op.body.target
        if   op.body.func == "add":      delta = BagAdd(op.body.args[0])
        elif op.body.func == "remove":   delta = BagRemove(op.body.args[0])
        elif op.body.func == "addFront": delta = ListAddFront(op.body.args[0])
        elif op.body.func == "addBack":  delta = ListAddBack(op.body.args[0])
        else: raise Exception("Unknown func: {}".format(op.body.func))
        return (member, delta)
    else:
        raise NotImplementedError(str(op.body))

@typechecked
def derivative(
        e     : syntax.Exp,
        var   : syntax.EVar,
        delta : Delta) -> (Delta, [syntax.Query]):
    """
    How does `e` change when `var` changes by `delta`?
    The answer may require some additional sub-queries to implement.
    """

    subgoals = []

    def derivative_makemap(d, key_func, value_func):
        if isinstance(d, NoDelta):
            return d
        elif isinstance(d, BagAdd) or isinstance(d, BagRemove):
            affected_key = key_func.apply_to(d.e)
            (subdelta, sgs) = derivative(value_func.body, value_func.arg, d)
            for sg in sgs:
                subgoals.append(sg)

            # If the subdelta is conditional, but the conditions don't depend on
            # the actual value, then we can push the map update inside the
            # condition for better performance.
            guards = []
            while isinstance(subdelta, Conditional) and not any(v == value_func.arg for v in free_vars(subdelta.cond)):
                guards.append(subdelta.cond)
                subdelta = subdelta.delta
            res = MapUpdate(affected_key, subdelta)
            if guards:
                res = Conditional(syntax.EAll(guards), res)
            return res
        elif isinstance(d, Conditional):
            return Conditional(
                d.cond,
                derivative_makemap(d.delta))
        else:
            raise NotImplementedError(d)

    def derivative_sum(d):
        if isinstance(d, NoDelta):
            return d
        elif isinstance(d, BagAdd):
            return AddNum(d.e)
        elif isinstance(d, BagRemove):
            return AddNum(syntax.EUnaryOp("-", d.e).with_type(e.type))
        elif isinstance(d, Conditional):
            return Conditional(
                d.cond,
                derivative_sum(d.delta))
        else:
            raise NotImplementedError(d)

    def derivative_map(d, proj):
        if isinstance(d, NoDelta):
            return d
        elif isinstance(d, BagAdd):
            return BagAdd(proj.apply_to(d.e))
        elif isinstance(d, BagRemove):
            return BagRemove(proj.apply_to(d.e))
        elif isinstance(d, Conditional):
            return Conditional(
                d.cond,
                derivative_map(d.delta, proj))
        else:
            raise NotImplementedError(d)

    def derivative_filter(d, cond):
        if isinstance(d, NoDelta):
            return d
        elif isinstance(d, BagAdd):
            return Conditional(cond.apply_to(d.e), BagAdd(d.e))
        elif isinstance(d, BagRemove):
            return Conditional(cond.apply_to(d.e), BagRemove(d.e))
        elif isinstance(d, Conditional):
            return Conditional(
                d.cond,
                derivative_filter(d.delta, cond))
        else:
            raise NotImplementedError(d)

    class V(Visitor):

        def visit_EVar(self, v):
            if v == var:
                return delta
            return NoDelta()

        def visit_EUnaryOp(self, e):
            if e.op == "sum":
                return derivative_sum(self.visit(e.e))
            else:
                raise NotImplementedError(e.op)

        def visit_EMap(self, e):
            if var in free_vars(e.f):
                # TODO: requires subgoals
                raise NotImplementedError(e)
            return derivative_map(self.visit(e.e), e.f)

        def visit_EFilter(self, e):
            if var in free_vars(e.p):
                # TODO: requires subgoals
                raise NotImplementedError(e)
            return derivative_filter(self.visit(e.e), e.p)

        def visit_EMakeMap(self, e):
            if var in free_vars(e.key) or var in free_vars(e.value):
                # TODO: requires subgoals
                raise NotImplementedError(e)
            return derivative_makemap(self.visit(e.e), e.key, e.value)

        def visit_EMakeRecord(self, e):
            return multi_delta([RecordFieldUpdate(f, self.visit(ee)) for (f, ee) in e.fields])

        def visit_Exp(self, e):
            raise NotImplementedError(str(e))

    change = V().visit(e)
    return (change, subgoals)

@typechecked
def apply_delta(
        x      : syntax.Exp,
        delta  : Delta) -> syntax.Stm:
    """
    Apply the given change to the given expression.
    """

    class V(Visitor):
        def visit_BagAdd(self, delta):
            return syntax.SCall(x, "BagAdd", [delta.e])
        def visit_BagRemove(self, delta):
            return syntax.SCall(x, "BagRemove", [delta.e])
        def visit_MapUpdate(self, delta):
            v = syntax.EVar(fresh_name()).with_type(x.type.v)
            return syntax.seq([
                syntax.SDecl(v.id, syntax.ECall("MapGet", [x, delta.key]).with_type(v.type)),
                apply_delta(v, delta.delta)])
        def visit_AddNum(self, delta):
            return syntax.SAssign(x, syntax.EBinOp(x, "+", delta.e))
        def visit_Conditional(self, delta):
            substm = self.visit(delta.delta)
            return syntax.SIf(delta.cond, substm, syntax.SNoOp())
        def visit_RecordFieldUpdate(self, delta):
            return apply_delta(syntax.EGetField(x, delta.f).with_type(dict(x.type.fields)[delta.f]), delta.delta)
        def visit_MultiDelta(self, delta):
            return syntax.SSeq(
                self.visit(delta.delta1),
                self.visit(delta.delta2))
        def visit_Delta(self, d):
            raise NotImplementedError(str(d))

    return V().visit(delta)
