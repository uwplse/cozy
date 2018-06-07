from cozy import common
from cozy import target_syntax
from cozy import syntax_tools
from cozy import solver

@common.typechecked
def uses_intrusive_data(e : target_syntax.Exp, handle : target_syntax.Exp) -> target_syntax.Exp:
    if isinstance(e, target_syntax.EMakeMap2):
        if e.e.type.t == handle.type:
            k = syntax_tools.fresh_var(e.type.k)
            return target_syntax.EImplies(
                target_syntax.EBinOp(k, target_syntax.BOp.In, e.e),
                uses_intrusive_data(e.value.apply_to(k), handle))
        return target_syntax.F
    elif isinstance(e, target_syntax.EFilter):
        return target_syntax.EAll([uses_intrusive_data(e.e, handle), e.p.apply_to(handle)])
    elif isinstance(e, target_syntax.EEmptyList):
        return target_syntax.F
    elif isinstance(e, target_syntax.EMap):
        return uses_intrusive_data(e.e, handle)
    elif isinstance(e, target_syntax.EUnaryOp):
        return uses_intrusive_data(e.e, handle)
    elif isinstance(e, target_syntax.EBinOp):
        return uses_intrusive_data(e.e1, handle) or uses_intrusive_data(e.e2, handle)
    elif isinstance(e, target_syntax.ECond):
        return target_syntax.ECond(e.cond,
            uses_intrusive_data(e.then_branch, handle),
            uses_intrusive_data(e.else_branch, handle)).with_type(target_syntax.BOOL)
    elif isinstance(e, target_syntax.ESingleton):
        if e.type.t == handle.type:
            return target_syntax.EEq(e.e, handle)
        return target_syntax.F
    elif isinstance(e, target_syntax.ETuple):
        return target_syntax.EAny(uses_intrusive_data(ee, handle) for ee in e.es)
    elif isinstance(e, target_syntax.EVar):
        if isinstance(e.type, target_syntax.TBag) and e.type.t == handle.type:
            return target_syntax.EBinOp(handle, target_syntax.BOp.In, e).with_type(target_syntax.BOOL)
        return target_syntax.F
    elif type(e) in [target_syntax.ENum, target_syntax.EBool, target_syntax.EEnumEntry]:
        return target_syntax.F
    else:
        raise NotImplementedError(e)

@common.typechecked
def compute_sharing(state_map : dict, true_types : dict) -> dict:
    """
    Takes a dictionary mapping { state_var_id : state_exp } and a
    dictionary mapping { state_var_id : refined_type } and returns
    a dictionary { ht : groups } for each handle type ht. Each group
    is a list of implementation types whose intrusive data will
    never be used at the same time.
    """

    types = set(t for e in state_map.values() for t in syntax_tools.all_types(e.type))
    handle_types = set(t for t in types if isinstance(t, target_syntax.THandle))
    out = { }

    # for (var, exp) in state_map.items():
    #     print(" --> {} = {}".format(var, syntax_tools.pprint(exp)))

    for ht in handle_types:
        groups = []
        handle = syntax_tools.fresh_var(ht, "handle")
        # print(ht)
        # for (var, exp) in state_map.items():
        #     print(" --> {} iff {}".format(var, syntax_tools.pprint(uses_intrusive_data(exp, handle))))

        type_uses_intrusive_data = { }
        for (var, exp) in state_map.items():
            use = uses_intrusive_data(exp, handle)
            for t in syntax_tools.all_types(true_types[var]):
                # print(syntax_tools.pprint(t))
                if hasattr(t, "intrusive_data"):
                    type_uses_intrusive_data[t] = use
                # else:
                #     print("     no intrusive data for " + syntax_tools.pprint(t))

        # print(type_uses_intrusive_data)

        for t, cond in type_uses_intrusive_data.items():
            found = False
            for g in groups:
                if all(not solver.satisfy(target_syntax.EAll([cond, type_uses_intrusive_data[t]])) for t in g):
                    found = True
                    g.append(t)
                    break
            if not found:
                groups.append([t])

        # print("    --> {}".format(groups))
        out[ht] = groups

    return out
