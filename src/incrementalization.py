from common import declare_case, Visitor
import syntax
from syntax_tools import subst

class Delta(object): pass
NoDelta         = declare_case(Delta, "NoDelta")
SetAdd          = declare_case(Delta, "SetAdd",          ["e"])
SetRemove       = declare_case(Delta, "SetRemove",       ["e"])
ListAddFront    = declare_case(Delta, "ListAddFront",    ["e"])
ListAddBack     = declare_case(Delta, "ListAddBack",     ["e"])
ListRemove      = declare_case(Delta, "ListRemove",      ["e"])

def to_delta(op):
    """
    Input: synax.Op
    Output: (name, [args], member, Delta) representing op's change
    """
    name = op.name
    args = op.args
    member = op.body.target
    if   op.body.func == "add":      delta = SetAdd(op.body.args[0])
    elif op.body.func == "remove":   delta = SetRemove(op.body.args[0])
    elif op.body.func == "addFront": delta = ListAddFront(op.body.args[0])
    elif op.body.func == "addBack":  delta = ListAddBack(op.body.args[0])
    else: raise Exception("Unknown func: {}".format(op.body.func))
    return (name, args, member, delta)

def delta_apply(e, member, delta):
    if isinstance(delta, SetAdd):
        return subst(e, { member : syntax.EBinOp(syntax.EVar(member), "union", syntax.EUnaryOp("singleton", delta.e)) })
    elif isinstance(delta, SetRemove):
        return subst(e, { member : syntax.EBinOp(syntax.EVar(member), "-", syntax.EUnaryOp("singleton", delta.e)) })
    else:
        raise NotImplementedError("unhandled case: {}".format(delta))

def change_to(e, var, delta):
    if isinstance(e, syntax.EVar):
        if e.id == var:
            return delta
        else:
            return NoDelta()
    else:
        raise NotImplementedError(e)
