from cozy.common import typechecked, fresh_name
from cozy.target_syntax import *
from cozy.typecheck import INT, BOOL, retypecheck, is_numeric
from cozy.syntax_tools import BottomUpRewriter, subst, fresh_var, all_types, all_exps, equal, implies, mk_lambda, compose, nnf, dnf, break_conj, pprint
from cozy.solver import valid
from cozy.opts import Option

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
def desugar_exp(e : Exp) -> Exp:
    class V(BottomUpRewriter):
        def visit_EMap(self, e):
            bag = self.visit(e.e)
            if isinstance(bag, EBinOp) and bag.op == "+":
                return self.visit(EBinOp(
                    EMap(bag.e1, e.f).with_type(e.type), "+",
                    EMap(bag.e2, e.f).with_type(e.type)).with_type(e.type))
            fbody = self.visit(e.f.body)
            if fbody == e.f.arg:
                return bag
            if isinstance(bag, EMap):
                return EMap(bag.e, compose(ELambda(e.f.arg, fbody), bag.f)).with_type(e.type)
            return EMap(bag, ELambda(e.f.arg, fbody)).with_type(e.type)
        def mk_filter_of_conjunction(self, bag : Exp, arg : EVar, conds : [Exp]) -> EFilter:
            return EFilter(bag, ELambda(arg, EAll(conds))).with_type(bag.type)
        def break_filter(self, e):
            if not break_disjunctive_filters.value or predicate_is_normal(e.p.body):
                # print("breaking normal-form filter: {}".format(pprint(e)))
                return e
            t = e.type
            arg = e.p.arg
            cases = dnf(nnf(e.p.body))
            negate = []
            res = None
            for case in cases:
                if res is None:
                    res = self.mk_filter_of_conjunction(e.e, arg, case)
                else:
                    res = EBinOp(res, "+", self.mk_filter_of_conjunction(e.e, arg, negate + case)).with_type(TBag(t.t))
                negate.append(ENot(EAll(case)))
            assert res is not None
            return res
        def visit_EFilter(self, e):
            # assert not hasattr(e, "broken")
            bag = self.visit(e.e)
            if isinstance(bag, EBinOp) and bag.op == "+":
                return self.visit(EBinOp(
                    EFilter(bag.e1, e.p).with_type(e.type), "+",
                    EFilter(bag.e2, e.p).with_type(e.type)).with_type(e.type))
            pbody = self.visit(e.p.body)
            if isinstance(bag, EFilter):
                return self.visit(EFilter(bag.e, ELambda(e.p.arg, EAll([pbody, bag.p.apply_to(e.p.arg)]))).with_type(e.type))
            if isinstance(bag, EMap):
                return self.visit(EMap(EFilter(bag.e, compose(ELambda(e.p.arg, pbody), bag.f)).with_type(bag.e.type), bag.f).with_type(e.type))
            return self.break_filter(EFilter(bag, ELambda(e.p.arg, pbody)).with_type(e.type))
        def visit_EFlatMap(self, e):
            bag = self.visit(e.e)
            fbody = self.visit(e.f.body)
            if isinstance(bag, EMap):
                e = EFlatMap(bag.e, compose(ELambda(e.f.arg, fbody), bag.f)).with_type(e.type)
            else:
                e = EFlatMap(bag, ELambda(e.f.arg, fbody)).with_type(e.type)
            bag = e.e
            fbody = e.f.body
            if isinstance(fbody, EMap):
                e = EMap(EFlatMap(bag, ELambda(e.f.arg, fbody.e)).with_type(TBag(fbody.e.type.t)), fbody.f).with_type(e.type)
            return e
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
        def visit_EUnaryOp(self, e):
            sub = self.visit(e.e)
            if e.op == UOp.Empty:
                arg = fresh_var(sub.type.t)
                return self.visit(EBinOp(
                    EUnaryOp(UOp.Sum, EMap(sub, ELambda(arg, ENum(1).with_type(INT))).with_type(TBag(INT))).with_type(INT),
                    "==",
                    ENum(0).with_type(INT)).with_type(BOOL))
            elif e.op == UOp.Any:
                arg = fresh_var(BOOL)
                return self.visit(ENot(EUnaryOp(UOp.Empty, EFilter(e.e, ELambda(arg, arg)).with_type(e.e.type)).with_type(e.type)))
            elif e.op == UOp.All:
                arg = fresh_var(BOOL)
                return self.visit(EUnaryOp(UOp.Empty, EFilter(e.e, ELambda(arg, ENot(arg))).with_type(e.e.type)).with_type(e.type))
            elif e.op == UOp.Exists:
                return self.visit(EUnaryOp(UOp.Not, EUnaryOp(UOp.Empty, e.e).with_type(BOOL)).with_type(BOOL))
            elif e.op == UOp.Sum:
                if isinstance(sub, EBinOp) and sub.op == "+":
                    return self.visit(EBinOp(
                        EUnaryOp(UOp.Sum, sub.e1).with_type(e.type), "+",
                        EUnaryOp(UOp.Sum, sub.e2).with_type(e.type)).with_type(e.type))
            return EUnaryOp(e.op, sub).with_type(e.type)
        def visit_EBinOp(self, e):
            e1 = self.visit(e.e1)
            e2 = self.visit(e.e2)
            op = e.op
            if op == "!=":
                return self.visit(ENot(EBinOp(e1, "==", e2).with_type(e.type)))
            elif op == BOp.In:
                return self.visit(ENot(equal(
                    ENum(0).with_type(INT),
                    EUnaryOp(UOp.Sum, EMap(EFilter(e.e2, mk_lambda(e.e2.type.t, lambda x: equal(x, e.e1))).with_type(e.e2.type), mk_lambda(e.e2.type.t, lambda x: ENum(1).with_type(INT))).with_type(TBag(INT))).with_type(INT))))
            elif op == "-" and is_numeric(e.type):
                return self.visit(EBinOp(e1, "+", EUnaryOp("-", e2).with_type(e.type)).with_type(e.type))
            else:
                return EBinOp(e1, op, e2).with_type(e.type)
        def visit_EFlatMap(self, e):
            return EFlatten(EMap(e.e, e.f).with_type(TBag(e.type))).with_type(e.type)
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
        list(spec.methods))
    for i in range(len(spec.statevars)):
        v, t = spec.statevars[i]
        if isinstance(t, TSet):
            t = TBag(t.t)
            spec.statevars[i] = (v, t)
            v = EVar(v).with_type(t)
            spec.assumptions.append(EUnaryOp("unique", v).with_type(BOOL))

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

    class V(BottomUpRewriter):
        def visit_Exp(self, e):
            return desugar_exp(e)
    spec = V().visit(spec)

    assert retypecheck(spec, env={})

    return spec
