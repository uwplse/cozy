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

def infer_rep(state : [EVar], qexp : Exp, validate_types : bool = False) -> [([(EVar, Exp)], Exp)]:
    """
    Given state vars and an expression, infer suitable representations for
    fast execution.
    """
    class V(Visitor):
        def visit_Exp(self, e):
            fvs = free_vars(e)
            assert fvs
            if all(v in state for v in fvs) and not isinstance(e, ELambda):
                v = fresh_var(e.type)
                yield ([(v, e)], v)
            else:
                children = e.children()
                expr_children = [i for i in range(len(children)) if isinstance(children[i], Exp)]
                for reps in cross_product([(self.visit(child) if isinstance(child, Exp) else (child,)) for child in e.children()]):
                    vs = sum((r[0] for (r, child) in zip(reps, e.children()) if isinstance(child, Exp)), [])
                    args = [r[1] if isinstance(child, Exp) else r for (r, child) in zip(reps, e.children())]
                    ee = type(e)(*args) #.with_type(e.type)
                    if hasattr(e, "type"):
                        ee = ee.with_type(e.type)
                    yield (vs, ee)
        def visit(self, e):
            fvs = free_vars(e)
            if fvs:
                yield from super().visit(e)
            else:
                yield ([], e)

    try:
        it = V().visit(qexp)
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
