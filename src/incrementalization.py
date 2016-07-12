from common import ADT, declare_case, Visitor, typechecked
import syntax
from syntax_tools import subst

class Delta(ADT): pass
NoDelta         = declare_case(Delta, "NoDelta")
SetAdd          = declare_case(Delta, "SetAdd",          ["e"])
SetRemove       = declare_case(Delta, "SetRemove",       ["e"])
# ListAddFront    = declare_case(Delta, "ListAddFront",    ["e"])
# ListAddBack     = declare_case(Delta, "ListAddBack",     ["e"])
# ListRemove      = declare_case(Delta, "ListRemove",      ["e"])
Conditional     = declare_case(Delta, "Conditional",     ["cond", "delta"])

Update = declare_case(ADT, "Update", ["var", "delta"])

@typechecked
def to_delta(op : syntax.Op) -> (str, [(str, syntax.Type)], syntax.Exp, Delta):
    """
    Input: synax.Op
    Output: (name, [args], member, Delta) representing op's change
    """
    name = op.name
    args = op.args
    if isinstance(op.body, syntax.SCall):
        member = op.body.target
        if   op.body.func == "add":      delta = SetAdd(op.body.args[0])
        elif op.body.func == "remove":   delta = SetRemove(op.body.args[0])
        elif op.body.func == "addFront": delta = ListAddFront(op.body.args[0])
        elif op.body.func == "addBack":  delta = ListAddBack(op.body.args[0])
        else: raise Exception("Unknown func: {}".format(op.body.func))
        return (name, args, member, delta)
    else:
        raise NotImplementedError(str(op.body))

def delta_apply(e, member, delta):
    if isinstance(delta, SetAdd):
        return subst(e, { member : syntax.EBinOp(syntax.EVar(member), "union", syntax.EUnaryOp("singleton", delta.e)) })
    elif isinstance(delta, SetRemove):
        return subst(e, { member : syntax.EBinOp(syntax.EVar(member), "-", syntax.EUnaryOp("singleton", delta.e)) })
    else:
        raise NotImplementedError("unhandled case: {}".format(delta))
