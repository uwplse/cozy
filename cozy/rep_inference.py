from cozy.common import Visitor, declare_case, cross_product
from cozy.target_syntax import *
from cozy.syntax_tools import fresh_var, free_vars, mk_lambda, subst, pprint, BottomUpRewriter, alpha_equivalent, compose

def _check_wt(state, input, output):
    from cozy.typecheck import retypecheck
    from cozy.syntax_tools import free_vars

    try:

        assert retypecheck(input)

        for (st, e) in output:
            assert all(v not in state for v in free_vars(e)), "output expression {} contains {}".format(pprint(e), [v for v in free_vars(e) if v in state])
            for (_, proj) in st:
                assert retypecheck(proj)
            assert retypecheck(e)

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

def dedup(vs : [(EVar, Exp)]) -> ([(EVar, Exp)], { EVar : EVar }):
    m = {}
    remap = {}
    for (v, e) in vs:
        ee = list(ee for ee in m.keys() if alpha_equivalent(e, ee))
        if ee:
            remap[v] = m[ee[0]]
        else:
            m[e] = v
    return ([(v, e) for (e, v) in m.items()], remap)

def pprint_rep(r):
    (st, e) = r
    print("-" * 20)
    for v, ve in st:
        print("{} = {}".format(pprint(v), pprint(ve)))
    print("return {}".format(pprint(e)))

def pprint_reps(r):
    for x in r:
        pprint_rep(x)

EAlterMapValues = declare_case(Exp, "EAlterMapValues", ["e", "f"])

def infer_rep(state : [EVar], qexp : Exp, validate_types : bool = False) -> [([(EVar, Exp)], Exp)]:
    """
    Given state vars and an expression, infer suitable representations for
    fast execution.
    """
    class V(Visitor):

        def apply_k(self, k, e):
            assert k.arg.type == e.type, "calling continuation {} on {}".format(pprint(k), pprint(e))
            if isinstance(e, EVar):
                e = k.apply_to(e)
                fvs = free_vars(e)
                st = [(fresh_var(v.type), v) for v in fvs if v in state]
                yield (st, subst(e, { old_var.id : new_var for (new_var, old_var) in st }))
            else:
                for (st, kk) in self.visit(k.body):
                    yield (st, subst(kk, { k.arg.id : e }))

        def visit_EFilter(self, e, k):
            fvs = free_vars(e.p)
            if e.p.arg not in free_vars(e.p.body):
                yield from self.visit(ECond(e.p.body, e.e, EEmptyList().with_type(e.type)).with_type(e.type), k=k)
            elif all(v in state for v in fvs):
                yield from self.visit(e.e, compose(k, mk_lambda(e.e.type, lambda x: EFilter(x, e.p).with_type(e.type))))
            else:
                for (st1, exp) in self.visit(e.e, mk_lambda(e.e.type, lambda x: x)):
                    for (st2, body2) in self.visit(e.p.body, mk_lambda(BOOL, lambda x: x)):
                        for (st3, res) in self.apply_k(k, EFilter(exp, ELambda(e.p.arg, body2)).with_type(e.type)):
                            yield (st1 + st2 + st3, res)
        def visit_EMap(self, e, k):
            fvs = free_vars(e.f)
            if all(v in state for v in fvs):
                yield from self.visit(e.e, compose(k, mk_lambda(e.e.type, lambda x: EMap(x, e.f).with_type(e.type))))
            else:
                for (st1, exp) in self.visit(e.e, mk_lambda(e.e.type, lambda x: x)):
                    for (st2, body2) in self.visit(e.f.body, mk_lambda(e.f.body.type, lambda x: x)):
                        for (st3, res) in self.apply_k(k, EMap(exp, ELambda(e.f.arg, body2)).with_type(e.type)):
                            yield (st1 + st2 + st3, res)
        def visit_EMakeMap(self, e, k):
            if not all(v in state for v in (free_vars(e.key) | free_vars(e.value))):
                return
            new_val = e.value
            while isinstance(k.body, EAlterMapValues):
                new_val = compose(k.body.f, new_val)
                k = ELambda(k.arg, k.body.e)
            yield from self.visit(e.e, compose(k, mk_lambda(e.e.type, lambda bag: EMakeMap(bag, e.key, new_val).with_type(TMap(e.type.k, new_val.body.type)))))
        def visit_EMapGet(self, e, k):
            if isinstance(e.map, EMakeMap):
                for (st1, key) in self.visit(e.key):
                    for (st2, m) in self.visit(e.map, k=mk_lambda(e.map.type, lambda m: EAlterMapValues(m, k).with_type(TMap(m.type.k, k.body.type)))):
                        yield (st1 + st2, EMapGet(m, key).with_type(m.type.v))
            else:
                yield from self.visit_Exp(e, k)
        def visit_EFlatMap(self, e, k):
            # TODO: if we can prove something about the cardinality of the set,
            # maybe we can materialize the join.
            for (outer_st, outer_exp) in self.visit(e.e, mk_lambda(e.e.type, lambda x: x)):
                for (inner_st, inner_exp) in self.visit(e.f.body, mk_lambda(e.f.body.type, lambda x: x)):
                    for (st3, res) in self.apply_k(k, EFlatMap(outer_exp, ELambda(e.f.arg, inner_exp)).with_type(e.type)):
                        yield (outer_st + inner_st + st3, res)
        def visit_Exp(self, e, k):
            fvs = free_vars(e)
            if not fvs:
                yield from self.apply_k(k, e)
            elif all(v in state for v in fvs):
                proj = k.apply_to(e)
                v = fresh_var(proj.type)
                yield ([(v, proj)], v)
            else:
                if any(isinstance(child, ELambda) for child in e.children()):
                    raise NotImplementedError(e)
                children = e.children()
                expr_children = [i for i in range(len(children)) if isinstance(children[i], Exp)]
                if len(expr_children) == 1:
                    i = expr_children[0]
                    echild = children[i]
                    kk = mk_lambda(echild.type, lambda new_child: type(e)(*[(children[j] if j != i else new_child) for j in range(len(children))]).with_type(e.type))
                    yield from self.visit(echild, k=compose(k, kk))
                else:
                    # for i in range(len(e.children())):
                    #     if isinstance(e.children()[i], Exp) and all(all(v in state for v in free_vars(e.children()[j])) for j in range(len(e.children())) if j != i and isinstance(e.children()[j], Exp)):
                    #         yield from self.visit(e.children()[i], k=compose(k, mk_lambda(e.children()[i].type, lambda new_child: type(e)(*[(e.children()[j] if j != i else new_child) for j in range(len(e.children()))]).with_type(e.type))))
                    for reps in cross_product([(self.visit(child) if isinstance(child, Exp) else (child,)) for child in e.children()]):
                        vs = sum((r[0] for (r, child) in zip(reps, e.children()) if isinstance(child, Exp)), [])
                        args = [r[1] if isinstance(child, Exp) else r for (r, child) in zip(reps, e.children())]
                        ee = type(e)(*args).with_type(e.type)
                        for st, res in self.apply_k(k, ee):
                            yield (st + vs, res)
        def visit(self, e, k=None):
            if k is None:
                k = mk_lambda(e.type, lambda x: x)
            assert k.arg.type == e.type
            fvs = free_vars(e)
            if fvs:
                yield from super().visit(e, k)
            else:
                yield from self.apply_k(k, e)

    try:
        it = V().visit(qexp, mk_lambda(qexp.type, lambda x: x))
        if validate_types:
            it = list(it)
            _check_wt(state, qexp, it)
        for (st, e) in it:
            st, remap = dedup(st)
            e = subst(e, { v1.id : v2 for (v1, v2) in remap.items() })
            yield (st, e)
    except Exception:
        print("Test case:")
        print("    infer_rep({}, {})".format(repr(state), repr(qexp)))
        raise
