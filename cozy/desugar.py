from cozy.common import typechecked, fresh_name
from cozy.target_syntax import *
from cozy.typecheck import retypecheck, is_numeric
from cozy.syntax_tools import BottomUpRewriter, subst, fresh_var, all_types, all_exps, equal, implies, mk_lambda, compose, nnf, dnf, break_conj, pprint
from cozy.solver import valid
from cozy.opts import Option
from cozy.evaluation import construct_value

break_disjunctive_filters = Option("break-disjunctive-filters", bool, False)

def predicate_is_normal(p):
    for part in break_conj(p):
        if isinstance(part, EUnaryOp) and part.op == "not":
            if not predicate_is_normal(part.e):
                return False
        elif isinstance(part, EBinOp) and part.op == "or":
            return False
    return True

@typechecked
def desugar_list_comprehensions(e : Exp) -> Exp:
    class V(BottomUpRewriter):
        def visit_EListComprehension(self, e):
            res, _, _ = self.visit_clauses(e.clauses, self.visit(e.e))
            return self.visit(res)
        def visit_clauses(self, clauses, final, i=0):
            if i >= len(clauses):
                return final, [], False
            clause = clauses[i]
            if isinstance(clause, CPull):
                bag = clause.e
                arg = EVar(clause.id).with_type(bag.type.t)
                rest, guards, pulls = self.visit_clauses(clauses, final, i + 1)
                if guards:
                    guard = guards[0]
                    for g in guards[1:]:
                        guard = EBinOp(guard, "and", g).with_type(BOOL)
                    bag = EFilter(bag, ELambda(arg, guard)).with_type(bag.type)
                if pulls:
                    res = EFlatMap(bag, ELambda(arg, rest)).with_type(rest.type)
                else:
                    res = EMap(bag, ELambda(arg, rest)).with_type(TBag(rest.type))
                return res, [], True
            elif isinstance(clause, CCond):
                rest, guards, pulls = self.visit_clauses(clauses, final, i + 1)
                return rest, guards + [clause.e], pulls
            else:
                raise NotImplementedError(clause)
    return V().visit(e)

@typechecked
def desugar(spec : Spec) -> Spec:

    # rewrite enums
    repl = {
        name : EEnumEntry(name).with_type(t)
        for t in all_types(spec)
        if isinstance(t, TEnum)
        for name in t.cases }
    spec = subst(spec, repl)

    # convert all collection types to bags
    spec = Spec(
        spec.name,
        list(spec.types),
        list(spec.extern_funcs),
        list(spec.statevars),
        list(spec.assumptions),
        list(spec.methods),
        spec.header,
        spec.footer)

    for i in range(len(spec.statevars)):
        v, t = spec.statevars[i]
        if isinstance(t, TSet):
            # Sets become bags w/ implicit unique assumptions.
            t = TBag(t.t)
            spec.statevars[i] = (v, t)
            v = EVar(v).with_type(t)
            spec.assumptions.append(EUnaryOp(UOp.AreUnique, v).with_type(BOOL))

    assert retypecheck(spec, env={})

    # organize queries by name
    queries = { q.name : q for q in spec.methods if isinstance(q, Query) }

    class V(BottomUpRewriter):
        def visit_ECall(self, e):
            q = queries.get(e.func)
            if q is not None:
                return self.visit(subst(q.ret, { arg_name: arg for ((arg_name, ty), arg) in zip(q.args, e.args) }))
            else:
                return ECall(e.func, tuple(self.visit(a) for a in e.args)).with_type(e.type)
    spec = V().visit(spec)
    spec.methods = [m for m in spec.methods if not (isinstance(m, Query) and m.visibility == Visibility.Private)]

    class V(BottomUpRewriter):
        def visit_Exp(self, e):
            return desugar_list_comprehensions(e)
    spec = V().visit(spec)

    assert retypecheck(spec, env={})

    return spec
