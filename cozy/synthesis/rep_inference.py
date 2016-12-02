from cozy.common import Visitor
from cozy.target_syntax import *
from cozy.syntax_tools import fresh_var, free_vars, mk_lambda

def compose(f1 : ELambda, f2 : ELambda) -> ELambda:
    return mk_lambda(f2.arg.type, lambda v: f1.apply_to(f2.apply_to(v)))

def infer_rep(state : [EVar], qexp : Exp) -> [([(EVar, Exp)], Exp)]:
    """
    Given state vars and an expression, infer suitable representations for
    fast execution.
    """
    class V(Visitor):
        def visit_EFilter(self, e, k):
            fvs = free_vars(e.p)
            if all(v in state for v in fvs):
                yield from self.visit(e.e, compose(k, mk_lambda(e.e.type, lambda x: EFilter(x, e.p).with_type(e.type))))
            else:
                for (st, exp) in self.visit(e.e, k):
                    yield (st, EFilter(exp, e.p).with_type(e.type))
        def visit_EMap(self, e, k):
            fvs = free_vars(e.f)
            if all(v in state for v in fvs):
                yield from self.visit(e.e, compose(k, mk_lambda(e.e.type, lambda x: EMap(x, e.f).with_type(e.type))))
            else:
                for (st, exp) in self.visit(e.e, k):
                    yield (st, EMap(exp, e.f).with_type(e.type))
        def visit_EMakeMap(self, e, k):
            assert type(e.type) is TMap
            fvs = free_vars(e.key) | free_vars(e.value)
            if all(v in state for v in fvs):
                new_val = compose(k, e.value)
                yield from self.visit(e.e, mk_lambda(e.e.type, lambda x: EMakeMap(x, e.key, new_val).with_type(TMap(e.type.k, new_val.body.type))))
            else:
                for (st, exp) in self.visit(e.e, k):
                    yield (st, EMakeMap(exp, e.key, e.value).with_type(e.type))
        def visit_EMapGet(self, e, k):
            for (st, exp) in self.visit(e.map, k):
                yield (st, EMapGet(exp, e.key).with_type(e.type))
        def visit_Exp(self, e, k):
            fvs = free_vars(e)
            if all(v in state for v in fvs):
                proj = k.apply_to(e)
                v = fresh_var(proj.type)
                yield ([(v, proj)], v)
            else:
                st = [(fresh_var(v.type), v) for v in fvs if v in state]
                yield (st, k.apply_to(e))
    yield from V().visit(qexp, mk_lambda(qexp.type, lambda x: x))
