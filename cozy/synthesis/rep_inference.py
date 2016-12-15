from cozy.common import Visitor
from cozy.target_syntax import *
from cozy.syntax_tools import fresh_var, free_vars, mk_lambda, subst

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
                for (st, exp) in self.visit(e.e, mk_lambda(e.e.type, lambda x: x)):
                    for (st2, body2) in self.visit(e.p.body, mk_lambda(e.e.type, lambda x: x)):
                        yield (st + st2, k.apply_to(EFilter(exp, ELambda(e.p.arg, body2)).with_type(e.type)))
        def visit_EMap(self, e, k):
            fvs = free_vars(e.f)
            if all(v in state for v in fvs):
                yield from self.visit(e.e, compose(k, mk_lambda(e.e.type, lambda x: EMap(x, e.f).with_type(e.type))))
            else:
                for (st, exp) in self.visit(e.e, mk_lambda(e.e.type, lambda x: x)):
                    for (st2, body2) in self.visit(e.f.body, mk_lambda(e.e.type, lambda x: x)):
                        yield (st + st2, k.apply_to(EMap(exp, ELambda(e.f.arg, body2)).with_type(e.type)))
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
        def visit_EUnaryOp(self, e, k):
            yield from self.visit(e.e, compose(k, mk_lambda(e.e.type, lambda x: EUnaryOp(e.op, x))))
        def visit_EFlatMap(self, e, k):
            # TODO: if we can prove something about the cardinality of the set,
            # maybe we can materialize the join.
            for (outer_st, outer_exp) in self.visit(e.e, mk_lambda(e.e.type, lambda x: x)):
                for (inner_st, inner_exp) in self.visit(e.f.body, k):
                    yield (outer_st + inner_st, EFlatMap(outer_exp, ELambda(e.f.arg, inner_exp)).with_type(e.type))
        def visit_EBinOp(self, e, k):
            for (st1, exp1) in self.visit(e.e1, mk_lambda(e.e1.type, lambda x: x)):
                for (st2, exp2) in self.visit(e.e2, mk_lambda(e.e2.type, lambda x: x)):
                    yield (st1 + st2, EBinOp(exp1, e.op, exp2).with_type(e.type))
        def visit_Exp(self, e, k):
            fvs = free_vars(e)
            if all(v in state for v in fvs):
                proj = k.apply_to(e)
                v = fresh_var(proj.type)
                yield ([(v, proj)], v)
            else:
                st = [(fresh_var(v.type), v) for v in fvs if v in state]
                yield (st, k.apply_to(subst(e, { old_var.id : new_var for (new_var, old_var) in st })))
    yield from V().visit(qexp, mk_lambda(qexp.type, lambda x: x))
