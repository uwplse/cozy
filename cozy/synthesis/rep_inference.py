from cozy.common import Visitor
from cozy.target_syntax import *
from cozy.syntax_tools import fresh_var, free_vars, mk_lambda, subst, pprint, BottomUpRewriter

def compose(f1 : ELambda, f2 : ELambda) -> ELambda:
    return mk_lambda(f2.arg.type, lambda v: f1.apply_to(f2.apply_to(v)))

def _check_wt(state, input, output):
    from cozy.typecheck import retypecheck
    from cozy.syntax_tools import free_vars

    env = { v.id:v.type for v in free_vars(input) }

    try:

        assert retypecheck(input, env)

        for (st, e) in output:
            assert all(v not in state for v in free_vars(e)), "output expression {} contains {}".format(pprint(e), [v for v in free_vars(e) if v in state])
            for (_, proj) in st:
                assert retypecheck(proj, env)
            assert retypecheck(e, env={ v.id:v.type for v in list(free_vars(input)) + [u for (u, proj) in st] })

    except:
        print("output was: {}".format(repr(output)))
        for (st, e) in output:
            for (sv, proj) in st:
                print("    {} : {} = {}".format(sv.id, pprint(sv.type), pprint(proj)))
            print("    return {}".format(pprint(e)))
        print("state vars: {}".format(repr(state)))
        for v in state:
            print("    {} : {}".format(pprint(v), pprint(v.type)))
        print("input was: {}".format(repr(input)))
        print("    {}".format(pprint(input)))
        raise

def infer_rep(state : [EVar], qexp : Exp, validate_types : bool = True) -> [([(EVar, Exp)], Exp)]:
    """
    Given state vars and an expression, infer suitable representations for
    fast execution.
    """
    class V(Visitor):

        def apply_k(self, k, e):
            e = k.apply_to(e)
            fvs = free_vars(e)
            st = [(fresh_var(v.type), v) for v in fvs if v in state]
            yield (st, subst(e, { old_var.id : new_var for (new_var, old_var) in st }))

        def visit_EFilter(self, e, k):
            fvs = free_vars(e.p)
            if all(v in state for v in fvs):
                yield from self.visit(e.e, compose(k, mk_lambda(e.e.type, lambda x: EFilter(x, e.p).with_type(e.type))))
            else:
                for (st1, exp) in self.visit(e.e, mk_lambda(e.e.type, lambda x: x)):
                    for (st2, body2) in self.visit(e.p.body, mk_lambda(e.e.type, lambda x: x)):
                        for (st3, res) in self.apply_k(k, EFilter(exp, ELambda(e.p.arg, body2)).with_type(e.type)):
                            yield (st1 + st2 + st3, res)
        def visit_EMap(self, e, k):
            fvs = free_vars(e.f)
            if all(v in state for v in fvs):
                yield from self.visit(e.e, compose(k, mk_lambda(e.e.type, lambda x: EMap(x, e.f).with_type(e.type))))
            else:
                for (st1, exp) in self.visit(e.e, mk_lambda(e.e.type, lambda x: x)):
                    for (st2, body2) in self.visit(e.f.body, mk_lambda(e.e.type, lambda x: x)):
                        for (st3, res) in self.apply_k(k, EMap(exp, ELambda(e.f.arg, body2)).with_type(e.type)):
                            yield (st1 + st2 + st3, res)
        def visit_EMakeMap(self, e, k):
            assert type(e.type) is TMap
            fvs = free_vars(e.key) | free_vars(e.value)
            if all(v in state for v in fvs):
                # Rewrite e.g. "k = (\m -> sum m[e])" into "k = (\vals -> sum vals)"
                karg = k.arg
                kbody = k.body
                vals = fresh_var(e.value.body.type)
                keys = []
                class Rewriter(BottomUpRewriter):
                    def visit_EMapGet(self, mg):
                        if mg.map == karg:
                            keys.append(mg.key)
                            return vals
                        else:
                            return mg
                new_k = ELambda(vals, Rewriter().visit(kbody))
                if len(keys) == 1 and all(v in state for v in free_vars(new_k)):
                    m = fresh_var(TMap(e.type.k, new_k.body.type))
                    mdef = EMakeMap(e.e, e.key, compose(new_k, e.value)).with_type(m.type)
                    for (st, res) in self.visit(keys[0], mk_lambda(m.type.k, lambda k: EMapGet(m, k).with_type(kbody.type))):
                        yield (st + [(m, mdef)], res)
        def visit_EMapGet(self, e, k):
            for (st1, key) in self.visit(e.key, mk_lambda(e.key.type, lambda x: x)):
                for (st2, get) in self.visit(e.map, compose(k, mk_lambda(e.map.type, lambda x: EMapGet(x, key).with_type(e.type)))):
                    yield (st2 + st1, get)
        def visit_EUnaryOp(self, e, k):
            yield from self.visit(e.e, compose(k, mk_lambda(e.e.type, lambda x: EUnaryOp(e.op, x))))
        def visit_EFlatMap(self, e, k):
            # TODO: if we can prove something about the cardinality of the set,
            # maybe we can materialize the join.
            for (outer_st, outer_exp) in self.visit(e.e, mk_lambda(e.e.type, lambda x: x)):
                for (inner_st, inner_exp) in self.visit(e.f.body, mk_lambda(e.f.body.type, lambda x: x)):
                    for (st3, res) in self.apply_k(k, EFlatMap(outer_exp, ELambda(e.f.arg, inner_exp)).with_type(e.type)):
                        yield (outer_st + inner_st + st3, res)
        def visit_EBinOp(self, e, k):
            fvs1 = free_vars(e.e1)
            fvs2 = free_vars(e.e2)
            if all(v in state for v in fvs1):
                yield from self.visit(e.e2, compose(k, mk_lambda(e.e2.type, lambda x: EBinOp(e.e1, e.op, x).with_type(e.type))))
            if all(v in state for v in fvs2):
                yield from self.visit(e.e1, compose(k, mk_lambda(e.e1.type, lambda x: EBinOp(x, e.op, e.e2).with_type(e.type))))
            for (st1, exp1) in self.visit(e.e1, mk_lambda(e.e1.type, lambda x: x)):
                for (st2, exp2) in self.visit(e.e2, mk_lambda(e.e2.type, lambda x: x)):
                    for (st3, res) in self.apply_k(k, EBinOp(exp1, e.op, exp2).with_type(e.type)):
                        yield (st1 + st2 + st3, res)
        def visit_Exp(self, e, k):
            fvs = free_vars(e)
            if all(v in state for v in fvs):
                proj = k.apply_to(e)
                v = fresh_var(proj.type)
                yield ([(v, proj)], v)
            else:
                yield from self.apply_k(k, e)
        def visit(self, e, k):
            fvs = free_vars(e)
            if fvs:
                yield from super().visit(e, k)
            else:
                yield from self.apply_k(k, e)

    it = V().visit(qexp, mk_lambda(qexp.type, lambda x: x))
    if validate_types:
        it = list(it)
        _check_wt(state, qexp, it)
    return it
