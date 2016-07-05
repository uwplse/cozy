from common import declare_case, Visitor
import syntax
from syntax_tools import subst

class Delta(object): pass
SetAdd    = declare_case(Delta, "SetAdd",    ["e"])
SetRemove = declare_case(Delta, "SetRemove", ["e"])

def to_delta(op):
    """
    Input: synax.Op
    Output: (name, [args], member, Delta) representing op's change
    """
    name = op.name
    args = op.args
    member = op.body.target
    if   op.body.func == "add":    delta = SetAdd(op.body.args[0])
    elif op.body.func == "remove": delta = SetRemove(op.body.args[0])
    else: raise Exception("Unknown func: {}".format(op.body.func))
    return (name, args, member, delta)

def delta_apply(e, args, member, delta):
    if isinstance(delta, SetAdd):
        return subst(e, { member : syntax.EBinOp(syntax.EVar(member), "union", syntax.EUnaryOp("singleton", syntax.EVar(args[0][0]))) })
    elif isinstance(delta, SetRemove):
        return subst(e, { member : syntax.EBinOp(syntax.EVar(member), "-", syntax.EUnaryOp("singleton", syntax.EVar(args[0][0]))) })
    else:
        raise NotImplementedError("unhandled case: {}".format(delta))
