from cozy.common import typechecked, fresh_name
from cozy.target_syntax import *
from cozy.typecheck import INT, BOOL, retypecheck
from cozy.syntax_tools import BottomUpRewriter, subst, fresh_var, all_types, all_exps, equal, implies, mk_lambda, compose, break_conj, pprint
from cozy.solver import valid

def _handleize(m : Method, statevar : EVar):
    class Rw(BottomUpRewriter):
        def visit_SCall(self, s):
            return s
        def visit_ELambda(self, e):
            if e.arg.id == statevar.id:
                return e
            return ELambda(e.arg, self.visit(e.body))
        def visit_EVar(self, v):
            if v == statevar:
                vt = statevar.type.t.value_type
                return EMap(v, mk_lambda(statevar.type.t, lambda handle: EGetField(handle, "val").with_type(vt))).with_type(TBag(vt))
            return v
    m = Rw().visit(m)
    if isinstance(m, Op):
        class Rw(BottomUpRewriter):
            def visit_SCall(self, s):
                target = self.visit(s.target)
                args = [self.visit(a) for a in s.args]
                if s.func == "add" and target == statevar:
                    args = [ENewHandle(args[0], statevar.type.t)]
                elif s.func == "remove" and target == statevar:
                    return SCall(target, "remove_all",
                        (EFilter(statevar, mk_lambda(statevar.type.t, lambda handle: equal(EGetField(handle, "val").with_type(statevar.type.t.value_type), args[0]))).with_type(TSet(statevar.type.t)),))
                return SCall(target, s.func, tuple(args))
        m = Rw().visit(m)
    return m

@typechecked
def desugar_exp(e : Exp) -> Exp:
    class V(BottomUpRewriter):
        def visit_EMap(self, e):
            bag = self.visit(e.e)
            fbody = self.visit(e.f.body)
            if fbody == e.f.arg:
                return bag
            if isinstance(bag, EMap):
                return EMap(bag.e, compose(ELambda(e.f.arg, fbody), bag.f)).with_type(e.type)
            return EMap(bag, ELambda(e.f.arg, fbody)).with_type(e.type)
        def break_filter(self, e):
            parts = list(break_conj(e.p.body))
            if len(parts) == 1:
                return e
            arg = e.p.arg
            e = e.e
            for p in parts:
                e = EFilter(e, ELambda(arg, p)).with_type(e.type)
            return e
        def visit_EFilter(self, e):
            bag = self.visit(e.e)
            pbody = self.visit(e.p.body)
            if isinstance(bag, EMap):
                return EMap(self.break_filter(EFilter(bag.e, compose(ELambda(e.p.arg, pbody), bag.f)).with_type(bag.e.type)), bag.f).with_type(e.type)
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
                bag = self.visit(clause.e)
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
                return rest, guards + [self.visit(clause.e)], pulls
            else:
                raise NotImplementedError(clause)
        def visit_EUnaryOp(self, e):
            sub = self.visit(e.e)
            if e.op == "empty":
                arg = fresh_var(sub.type.t)
                return self.visit(EBinOp(
                    EUnaryOp("sum", EMap(sub, ELambda(arg, ENum(1).with_type(INT))).with_type(TBag(INT))).with_type(INT),
                    "==",
                    ENum(0).with_type(INT)).with_type(BOOL))
            elif e.op == "any":
                arg = fresh_var(BOOL)
                return self.visit(ENot(EUnaryOp("empty", EFilter(e.e, ELambda(arg, arg)).with_type(e.e.type)).with_type(e.type)))
            elif e.op == "all":
                arg = fresh_var(BOOL)
                return self.visit(EUnaryOp("empty", EFilter(e.e, ELambda(arg, ENot(arg))).with_type(e.e.type)).with_type(e.type))
            else:
                return EUnaryOp(e.op, sub).with_type(e.type)
        def visit_EBinOp(self, e):
            e1 = self.visit(e.e1)
            e2 = self.visit(e.e2)
            op = e.op
            if op == "!=":
                return self.visit(ENot(EBinOp(e1, "==", e2).with_type(e.type)))
            elif op == "in":
                return self.visit(ENot(equal(
                    ENum(0).with_type(INT),
                    EUnaryOp("sum", EMap(EFilter(e.e2, mk_lambda(e.e2.type.t, lambda x: equal(x, e.e1))).with_type(e.e2.type), mk_lambda(e.e2.type.t, lambda x: ENum(1).with_type(INT))).with_type(TBag(INT))).with_type(INT))))
            else:
                return EBinOp(e1, op, e2).with_type(e.type)
        def visit_EFlatMap(self, e):
            return EFlatten(EMap(e.e, e.f))
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

    # convert all collection types to bags of handles
    spec = Spec(
        spec.name,
        list(spec.types),
        list(spec.extern_funcs),
        list(spec.statevars),
        list(spec.assumptions),
        list(spec.methods))
    for i in range(len(spec.statevars)):
        v, t = spec.statevars[i]
        v = EVar(v).with_type(t)
        if isinstance(t, TSet):
            t = TBag(t.t)
            spec.statevars[i] = (v.id, t)
            v = EVar(v.id).with_type(t)
            spec.assumptions.append(EUnaryOp("unique", v).with_type(BOOL))
            assert retypecheck(spec, env=())
        if isinstance(t, TBag):
            if not isinstance(t.t, THandle) or not valid(desugar_exp(implies(EAll(spec.assumptions), EUnaryOp("unique", v).with_type(BOOL)))):
                orig_t = t
                ht = THandle(fresh_name("HandleType"), t.t)
                t = TBag(ht)
                v = EVar(v.id).with_type(t)
                spec.statevars[i] = (v.id, t)
                spec.assumptions = [_handleize(a, v) for a in spec.assumptions]
                spec.assumptions.append(EUnaryOp("unique", v).with_type(BOOL))
                spec.methods = [_handleize(m, v) for m in spec.methods]
        else:
            raise NotImplementedError(t)

    assert retypecheck(spec, env=())

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
    for ee in all_exps(spec):
        if isinstance(ee, ELambda):
            if not isinstance(ee.arg.type, THandle):
                import pdb
                pdb.set_trace()
                assert False

    return spec
