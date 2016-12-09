from cozy.common import ADT, declare_case, Visitor, typechecked, fresh_name
from cozy import syntax
from cozy import target_syntax
from cozy.syntax_tools import subst, free_vars, pprint, equal

# General deltas
class Delta(ADT): pass
NoDelta           = declare_case(Delta, "NoDelta")
Conditional       = declare_case(Delta, "Conditional",     ["cond", "delta"])
MultiDelta        = declare_case(Delta, "MultiDelta",      ["delta1", "delta2"])
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

def _push_delta_through_field_access(members, lhs, delta):
    if isinstance(lhs, syntax.EVar):
        if isinstance(lhs.type, syntax.THandle):
            bag = syntax.EVar(lhs.type.statevar).with_type(members[lhs.type.statevar])
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
        if   op.body.func == "add":      delta = BagAdd(op.body.args[0])
        elif op.body.func == "remove":   delta = BagRemove(op.body.args[0])
        elif op.body.func == "addFront": delta = ListAddFront(op.body.args[0])
        elif op.body.func == "addBack":  delta = ListAddBack(op.body.args[0])
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

    subgoals = []

    def make_subgoal(e):
        fvs = free_vars(e)
        if not any(v in ctx for v in fvs):
            return e
        query_name = fresh_name()
        query_vars = [v for v in fvs if v not in ctx]
        query = syntax.Query(query_name, [(arg.id, arg.type) for arg in query_vars], [], e)
        subgoals.append(query)
        return syntax.ECall(query_name, query_vars).with_type(e.type)

    def recurse(*args, **kwargs):
        (res, sgs) = derivative(*args, **kwargs)
        subgoals.extend(sgs)
        return res

    def derivative_makemap(d, key_func, value_func):
        if isinstance(d, NoDelta):
            return d
        elif isinstance(d, BagAdd) or isinstance(d, BagRemove):
            affected_key = key_func.apply_to(d.e)
            (subdelta, sgs) = derivative(value_func.body, value_func.arg, d, ctx)
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
                res = mk_conditional(syntax.EAll(guards), res)
            return res
        elif isinstance(d, BagElemUpdated):
            affected_key = key_func.apply_to(d.elem)
            key_delta = recurse(key_func.body, key_func.arg, d.delta, ctx)
            if isinstance(key_delta, NoDelta):
                return MapUpdate(affected_key, recurse(value_func.body, value_func.arg, BagElemUpdated(d.elem, d.delta), ctx))
            else:
                new_key = apply_delta(key_func.apply_to(d.elem), key_delta)
                on_rm = recurse(value_func.body, value_func.arg, BagRemove(d.elem), ctx)
                on_add = recurse(value_func.body, value_func.arg, BagAdd(d.elem), ctx) # TODO: BagAdd(apply_delta(d.elem), d.delta)
                return multi_delta([
                    MapUpdate(affected_key, on_rm),
                    MapUpdate(new_key, on_add)])

            # raise NotImplementedError(key_delta)

            # new_key = key_func.apply_to(apply_delta(d.elem, d.delta))
            # on_add = recurse(value_func.body, value_func.arg, BagAdd(d.elem), ctx)
            # on_rm = recurse(value_func.body, value_func.arg, BagRemove(d.elem), ctx)
            # on_mod = recurse(value_func.body, value_func.arg, BagElemUpdated(d.elem, d.delta), ctx)
            # return multi_delta([
            #     mk_conditional(syntax.ENot(equal(affected_key, new_key)), multi_delta([
            #         MapUpdate(affected_key, on_rm),
            #         MapUpdate(new_key, on_add)])),
            #     mk_conditional(equal(affected_key, new_key),
            #         MapUpdate(affected_key, on_mod))])
            # raise NotImplementedError()
        elif isinstance(d, Conditional):
            return mk_conditional(
                d.cond,
                derivative_makemap(d.delta, key_func, value_func))
        else:
            raise NotImplementedError(d)

    def derivative_sum(d):
        if isinstance(d, NoDelta):
            return d
        elif isinstance(d, BagAdd):
            return AddNum(d.e)
        elif isinstance(d, BagAddAll):
            return AddNum(syntax.EUnaryOp("sum", d.e).with_type(d.e.type.t))
        elif isinstance(d, BagRemove):
            return AddNum(syntax.EUnaryOp("-", d.e).with_type(d.e.type))
        elif isinstance(d, BagElemUpdated):
            if isinstance(d.delta, NoDelta):
                return d.delta
            elif isinstance(d.delta, AddNum):
                return d.delta
            else:
                # TODO: requires subgoals
                raise NotImplementedError("update sum: " + d)
        else:
            raise NotImplementedError(d)

    def derivative_the(d):
        if isinstance(d, BagAdd):
            return Become(syntax.EJust(d.e))
        elif isinstance(d, BagRemove):
            return Become(syntax.ENull().with_type(syntax.TMaybe(d.e.type)))
        elif isinstance(d, BagElemUpdated):
            return NoDelta()
        else:
            raise NotImplementedError(d)

    def derivative_map(d, proj):
        if isinstance(d, NoDelta):
            return d
        elif isinstance(d, BagAdd):
            return BagAdd(proj.apply_to(d.e))
        elif isinstance(d, BagAddAll):
            return BagAddAll(target_syntax.EMap(d.e, proj).with_type(syntax.TBag(proj.body.type)))
        elif isinstance(d, BagRemove):
            return BagRemove(proj.apply_to(d.e))
        elif isinstance(d, BagElemUpdated):
            change = recurse(proj.body, proj.arg, d.delta, ctx)
            elem = proj.apply_to(d.elem)
            return BagElemUpdated(elem, change)
        elif isinstance(d, Conditional):
            return mk_conditional(
                d.cond,
                derivative_map(d.delta, proj))
        elif isinstance(d, MultiDelta):
            return multi_delta([
                derivative_map(d.delta1, proj),
                derivative_map(d.delta2, proj)])
        else:
            raise NotImplementedError(d)

    def derivative_filter(d, cond):
        if isinstance(d, NoDelta):
            return d
        elif isinstance(d, BagAdd):
            return mk_conditional(cond.apply_to(d.e), BagAdd(d.e))
        elif isinstance(d, BagRemove):
            return mk_conditional(cond.apply_to(d.e), BagRemove(d.e))
        elif isinstance(d, BagElemUpdated):
            containment_change = recurse(cond.body, cond.arg, d.delta, ctx)
            if isinstance(containment_change, NoDelta):
                return mk_conditional(cond.apply_to(d.elem), d)
            else:
                contained = cond.apply_to(d.elem)
                now_contains = apply_delta(contained, containment_change)
                return multi_delta([
                    mk_conditional(syntax.EAll([contained, syntax.ENot(now_contains)]), BagRemove(d.elem)),
                    mk_conditional(syntax.EAll([syntax.ENot(contained), now_contains]), BagAdd(d.elem))])
        else:
            raise NotImplementedError(d)

    class V(Visitor):

        def visit_EVar(self, v):
            if v == var:
                return delta
            return NoDelta()

        def visit_ENum(self, e):
            return NoDelta()
        def visit_EBool(self, e):
            return NoDelta()
        def visit_EEnumEntry(self, e):
            return NoDelta()

        def visit_ECall(self, call):
            deltas = [self.visit(arg) for arg in call.args]
            if all(d == NoDelta() for d in deltas):
                return NoDelta()
            else:
                return Become(syntax.ECall(call.func, [apply_delta(arg, delta) for (arg, delta) in zip(call.args, deltas)]))

        def visit_EGetField(self, e):
            subdelta = self.visit(e.e)
            def xform(d):
                if isinstance(d, NoDelta):
                    return d
                elif isinstance(d, RecordFieldUpdate):
                    return d.delta if d.f == e.f else NoDelta()
                else:
                    raise Exception(d)
            return map_cond(subdelta, xform)

        def visit_EUnaryOp(self, e):
            if e.op == "sum":
                return map_cond(self.visit(e.e), derivative_sum)
            elif e.op == "not":
                return rewrite_becomes(self.visit(e.e), lambda e: syntax.EUnaryOp("not", e).with_type(syntax.TBool()))
            elif e.op == "the":
                return map_cond(self.visit(e.e), derivative_the)
            else:
                raise NotImplementedError(e.op)

        def visit_EBinOp(self, e):
            v1 = e.e1 #make_subgoal(e.e1)
            v2 = e.e2 #make_subgoal(e.e2)
            v1d = self.visit(e.e1)
            v2d = self.visit(e.e2)
            if isinstance(v1d, NoDelta) and isinstance(v2d, NoDelta):
                return v1d
            if e.op == "==" and type(e.e1.type) in [syntax.TInt, syntax.TLong, syntax.TBool, syntax.TEnum]:
                return Become(syntax.EBinOp(apply_delta(v1, v1d), "==", apply_delta(v2, v2d)).with_type(syntax.TBool()))
            elif e.op == "or" or e.op == "and":
                return Become(syntax.EBinOp(apply_delta(v1, v1d), e.op, apply_delta(v2, v2d)).with_type(syntax.TBool()))
            else:
                raise NotImplementedError("{} over {}, {}".format(e.op, e.e1.type, e.e2.type))

        def visit_EMap(self, e):
            if var in free_vars(e.f):
                # TODO: requires subgoals
                raise NotImplementedError(e)
            return derivative_map(self.visit(e.e), e.f)

        def visit_EFilter(self, e):
            if var in free_vars(e.p):
                # Rename argument to avoid trouble
                arg = syntax.EVar(fresh_name()).with_type(e.p.arg.type)
                cond = subst(e.p.body, { e.p.arg.id : arg })

                # How does the condition change?
                cond_delta, sgs = derivative(cond, var, delta, ctx)
                # print("cond = {} [contains {}]".format(pprint(cond), var.id))
                # print("cond delta [{} // {}] = {}".format(var, delta, cond_delta))
                subgoals.extend(sgs)
                new_cond = apply_delta(cond, cond_delta)

                # What elements are entering or exiting the set?
                # This might be difficult to compute, so we fork it off as a subgoal.
                enter = make_subgoal(target_syntax.EFilter(
                    e.e,
                    target_syntax.ELambda(arg, syntax.EAll([syntax.EUnaryOp("not", cond), new_cond]))).with_type(e.type))
                exit = make_subgoal(target_syntax.EFilter(
                    e.e,
                    target_syntax.ELambda(arg, syntax.EAll([syntax.EUnaryOp("not", new_cond), cond]))).with_type(e.type))
                rest = map_cond(self.visit(e.e), lambda d: derivative_filter(d, target_syntax.ELambda(arg, new_cond)))

                return multi_delta([
                    BagAddAll(enter),
                    BagAddAll(exit),
                    rest])
            return map_cond(self.visit(e.e), lambda d: derivative_filter(d, e.p))

        def visit_EMakeMap(self, e):
            if var in free_vars(e.key) or var in free_vars(e.value):
                # TODO: requires subgoals
                raise NotImplementedError(e)
            return derivative_makemap(self.visit(e.e), e.key, e.value)

        def visit_EMakeRecord(self, e):
            return multi_delta([RecordFieldUpdate(f, self.visit(ee)) for (f, ee) in e.fields])

        def visit_ETuple(self, e):
            return multi_delta([mk_TupleEntryUpdate(i, self.visit(e.es[i])) for i in range(len(e.es))])

        # def visit(self, e):
        #     res = super().visit(e)
        #     print("{} [{} // {}] ---> {}".format(pprint(e), var, delta, res))
        #     return res

        def visit_Exp(self, e):
            raise NotImplementedError(str(e))

    change = V().visit(e)
    change = rewrite_becomes(change, make_subgoal)
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
        def visit_Conditional(self, delta):
            return syntax.ECond(delta.cond, self.visit(delta.delta), x).with_type(x.type)
        def visit_MultiDelta(self, delta):
            return apply_delta(apply_delta(x, delta.delta1), delta.delta2)
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
        def visit_BagRemove(self, delta):
            return syntax.SCall(x, "remove", [delta.e])
        def visit_BagElemUpdated(self, delta):
            return syntax.SNoOp()
        def visit_MapUpdate(self, delta):
            v = syntax.EVar(fresh_name()).with_type(x.type.v)
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
        def visit_MultiDelta(self, delta):
            return syntax.SSeq(
                self.visit(delta.delta1),
                self.visit(delta.delta2))
        def visit_Delta(self, d):
            raise NotImplementedError(str(d))

    return V().visit(delta)
