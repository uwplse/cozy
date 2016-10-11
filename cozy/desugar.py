from cozy.common import typechecked
from cozy.target_syntax import *
from cozy.syntax_tools import BottomUpRewriter

@typechecked
def desugar(spec : Spec) -> Spec:

    queries = { q.name : q for q in spec.methods if isinstance(q, Query) }

    class V(BottomUpRewriter):
        def visit_ECall(self, e):
            if e.func in queries:
                raise NotImplementedError()
            else:
                return ECall(e.f, tuple(self.visit(a) for a in e.args))
        def visit_EListComprehension(self, e):
            res, _, _ = self.visit_clauses(e.clauses, self.visit(e.e))
            return res
        def visit_clauses(self, clauses, final, i=0):
            if i >= len(clauses):
                return final, [], False
            clause = clauses[i]
            if isinstance(clause, CPull):
                bag = self.visit(clause.e)
                arg = EVar(clause.id).with_type(bag.type.t)
                rest, guards, pulls = self.visit_clauses(clauses, final, i + 1)
                if guards:
                    guard = guards[0]
                    for g in guards[1:]:
                        guard = EBinOp(guard, "and", g).with_type(BOOL)
                    bag = EFilter(bag, ELambda(arg, guard)).with_type(bag.type)
                res = EMap(bag, ELambda(arg, rest)).with_type(TBag(rest.type))
                if pulls:
                    res = EFlatten(res)
                return res, [], True
            elif isinstance(clause, CCond):
                rest, guards, pulls = self.visit_clauses(clauses, final, i + 1)
                return rest, guards + [self.visit(clause.e)], pulls
            else:
                raise NotImplementedError(clause)
        def visit_EUnaryOp(self, e):
            sub = self.visit(e.e)
            if e.op == "empty":
                arg = EVar(fresh_name()).with_type(sub.type.t)
                return EBinOp(
                    EUnaryOp("sum", EMap(sub, ELambda(arg, ENum(1).with_type(INT))).with_type(TBag(INT))).with_type(INT),
                    "==",
                    ENum(0).with_type(INT)).with_type(BOOL)
            else:
                return EUnaryOp(e.op, sub).with_type(e.type)

    return V().visit(spec)
