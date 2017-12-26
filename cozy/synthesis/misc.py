from cozy.syntax import Query, EAll, EImplies, EEq
from cozy.solver import valid

def rewrite_ret(q : Query, repl, keep_assumptions=True) -> Query:
    return Query(
        q.name,
        q.visibility,
        q.args,
        q.assumptions if keep_assumptions else (),
        repl(q.ret),
        q.docstring)

def queries_equivalent(q1 : Query, q2 : Query):
    if q1.ret.type != q2.ret.type:
        return False
    q1args = dict(q1.args)
    q2args = dict(q2.args)
    if q1args != q2args:
        return False
    q1a = EAll(q1.assumptions)
    q2a = EAll(q2.assumptions)
    return valid(EEq(q1a, q2a)) and valid(EImplies(q1a, EEq(q1.ret, q2.ret)))
