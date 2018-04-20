from cozy.syntax import Query, EAll, EImplies, EEq
from cozy.solver import valid
from cozy.logging import task

def queries_equivalent(q1 : Query, q2 : Query):
    with task("checking query equivalence", q1=q1.name, q2=q2.name):
        if q1.ret.type != q2.ret.type:
            return False
        q1args = dict(q1.args)
        q2args = dict(q2.args)
        if q1args != q2args:
            return False
        q1a = EAll(q1.assumptions)
        q2a = EAll(q2.assumptions)
        return valid(EEq(q1a, q2a)) and valid(EImplies(q1a, EEq(q1.ret, q2.ret)))
