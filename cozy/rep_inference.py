from cozy.common import OrderedSet
from cozy.target_syntax import *
from cozy.syntax_tools import pprint, alpha_equivalent, subst, enumerate_fragments, fresh_var

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
    Separate an expression into the concrete-state component and the runtime
    component.
    """

    state = OrderedSet(state)
    new_state = []
    dirty = True
    while dirty:
        dirty = False
        for (_, e, r) in enumerate_fragments(qexp):
            needs_rewrite = False
            if isinstance(e, EStateVar):
                needs_rewrite = True
                e = e.e
            elif isinstance(e, EVar) and e in state:
                needs_rewrite = True
            if needs_rewrite:
                v = fresh_var(e.type)
                new_state.append((v, e))
                qexp = r(v)
                dirty = True
                break

    try:
        if validate_types:
            _check_wt(state, qexp, [(new_state, qexp)])
        st, remap = dedup(new_state)
        qexp = subst(qexp, { v1.id : v2 for (v1, v2) in remap.items() })
        yield (st, qexp)
    except Exception:
        print("Test case:")
        print("    infer_rep({}, {})".format(repr(state), repr(qexp)))
        raise
