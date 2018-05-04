import itertools

from cozy.common import FrozenDict
from cozy.syntax import Query, TFunc, EVar, EAll, EImplies, EEq
from cozy.solver import ModelCachingSolver
from cozy.logging import task

_qe_cache = { }

def queries_equivalent(q1 : Query, q2 : Query, state_vars : [EVar], extern_funcs : { str : TFunc }):
    with task("checking query equivalence", q1=q1.name, q2=q2.name):
        if q1.ret.type != q2.ret.type:
            return False
        q1args = dict(q1.args)
        q2args = dict(q2.args)
        if q1args != q2args:
            return False
        args = FrozenDict(q1args)

        checker = _qe_cache.get(args)
        if checker is None:
            checker = ModelCachingSolver(
                vars = list(itertools.chain(state_vars, (EVar(v).with_type(t) for v, t in args.items()))),
                funcs = extern_funcs)
            _qe_cache[args] = checker

        q1a = EAll(q1.assumptions)
        q2a = EAll(q2.assumptions)
        return checker.valid(EEq(q1a, q2a)) and checker.valid(EImplies(q1a, EEq(q1.ret, q2.ret)))
