from cozy.common import typechecked
from cozy.target_syntax import *
from cozy.typecheck import INT, BOOL
from cozy.syntax_tools import BottomUpRewriter, subst, fresh_var, all_types

@typechecked
def desugar(spec : Spec) -> Spec:

    # rewrite enums
    repl = {
        name : EEnumEntry(name).with_type(t)
        for t in all_types(spec)
        if isinstance(t, TEnum)
        for name in t.cases }
    spec = subst(spec, repl)

    queries = { q.name : q for q in spec.methods if isinstance(q, Query) }

    class V(BottomUpRewriter):
        def visit_ECall(self, e):
            q = queries.get(e.func)
            if q is not None:
                return self.visit(subst(q.ret, { arg_name: arg for ((arg_name, ty), arg) in zip(q.args, e.args) }))
            else:
                return ECall(e.func, tuple(self.visit(a) for a in e.args)).with_type(e.type)
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
                    res = EFlatten(res).with_type(res.type.t)
                return res, [], True
            elif isinstance(clause, CCond):
                rest, guards, pulls = self.visit_clauses(clauses, final, i + 1)
                return rest, guards + [self.visit(clause.e)], pulls
            else:
                raise NotImplementedError(clause)
        def visit_EUnaryOp(self, e):
            sub = self.visit(e.e)
            if e.op == "empty":
                arg = fresh_var(sub.type.t)
                return EBinOp(
                    EUnaryOp("sum", EMap(sub, ELambda(arg, ENum(1).with_type(INT))).with_type(TBag(INT))).with_type(INT),
                    "==",
                    ENum(0).with_type(INT)).with_type(BOOL)
            elif e.op == "any":
                arg = fresh_var(BOOL)
                return self.visit(ENot(EUnaryOp("empty", EFilter(e.e, ELambda(arg, arg)).with_type(e.e.type)).with_type(e.type)))
            elif e.op == "all":
                arg = fresh_var(BOOL)
                return self.visit(EUnaryOp("empty", EFilter(e.e, ELambda(arg, ENot(arg))).with_type(e.e.type)).with_type(e.type))
            else:
                return EUnaryOp(e.op, sub).with_type(e.type)

    return V().visit(spec)
