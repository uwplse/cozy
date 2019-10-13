import random
import string
from itertools import product

from cozy.common import FrozenDict
from cozy.contexts import RootCtx
from cozy.syntax import *
from cozy.syntax_tools import free_vars, pprint
from cozy.evaluation import eval
from cozy.target_syntax import EFlatMap, EFilter, EMap, EStateVar

# FIXME: how to use solver for this purpose?
from cozy.value_types import Bag

def random_value(t):
    if isinstance(t, TBag):
        yield Bag()
        for v in random_value(t.elem_type):
            yield Bag((v,))
        for v1 in random_value(t.elem_type):
            for v2 in random_value(t.elem_type):
                yield Bag((v1, v2))
    elif isinstance(t, TInt):
        yield random.randint(0, 100)
        yield 0
    elif isinstance(t, TFloat):
        yield random.randint(0, 100) / 100.0
        yield 0.0
    elif isinstance(t, TBool):
        yield True
        yield False
    elif isinstance(t, TString):
        yield ''.join(random.choice(string.ascii_letters) for _ in range(8))
    elif isinstance(t, TRecord):
        iterables = [ random_value(ty) for _, ty in t.fields ]
        for vs in product(*iterables):
            yield FrozenDict({ field[0] : v for v, field in zip(vs, t.fields) })
    else:
        raise Exception("Unknown type for random value construction: {}".format(t))


def get_pulled(e):
    if isinstance(e, EStateVar):
        return e.e
    return e

def extract_listcomp(e):
    if isinstance(e, EFlatMap):
        pulled = e.e
        f = e.transform_function
        var = f.arg
        ebody = f.body
        lc = extract_listcomp(ebody)
        lc["P"][var] = get_pulled(pulled)
        return lc
    elif isinstance(e, EMap):
        f = e.transform_function
        var = f.arg
        ebody = f.body
        lc = extract_listcomp(e.e)
        lc["V"] = ebody
        return lc
    elif isinstance(e, EFilter):
        lc = { "C": e.predicate.body, "P": { e.predicate.arg: get_pulled(e.e) } }
        return lc

def print_lc(lc):
    print("Pulls: " + ", ".join(pprint(var) + ": " + pprint(p) for var, p in lc["P"].items()))
    print("Cond: " + pprint(lc["C"]))
    print("Value: " + pprint(lc["V"]))
    print()

def get_cond(lc):
    singletons = [EEq(ESingleton(var).with_type(TBag(var.type)), p) for var, p in lc["P"].items()]
    return EAll([lc["C"]] + singletons)

def notvalid(e):
    if isinstance(e, EUnaryOp) and e.op == "not" and isinstance(e.e, EBinOp) and e.e.op == "==":
        e1 = e.e.e1
        e2 = e.e.e2
        while isinstance(e1, EStateVar):
            e1 = e1.e
        while isinstance(e2, EStateVar):
            e2 = e2.e
        if isinstance(e1, EFlatMap) and isinstance(e2, EFlatMap):
            lc1 = extract_listcomp(e1)
            lc2 = extract_listcomp(e2)
            if lc1 is not None and lc2 is not None:
                if lc1 == lc2:
                    return True
    return None

def satisfy(e):
    from cozy.solver import solver_for_context
    context = RootCtx()
    solver = solver_for_context(context)

    if isinstance(e, EUnaryOp) and e.op == "not" and isinstance(e.e, EBinOp) and e.e.op == "==":
        e1 = e.e.e1
        e2 = e.e.e2
        if isinstance(e1, EFlatMap) and isinstance(e2, EFlatMap):
            lc1 = extract_listcomp(e1)
            lc2 = extract_listcomp(e2)
            if lc1 is not None and lc2 is not None:
                cond1 = get_cond(lc1)
                cond2 = get_cond(lc2)
                sat1 = solver.satisfy(cond1)
                sat2 = solver.satisfy(cond2)
                if sat1 is None and sat2 is not None:
                    return { k: v for k, v in sat2.items() if k not in lc2["P"] }
                if sat1 is not None and sat2 is None:
                    return { k: v for k, v in sat1.items() if k not in lc1["P"] }

    iterables = [ random_value(v.type) for v in free_vars(e) ]
    ids = [ v.id for v in free_vars(e) ]
    for vs in product(*iterables):
        assignments = {}
        for id, val in zip(ids, vs):
            assignments[id] = val
        # print("[DEBUG]: assignments: %s" % assignments)
        sat = eval(e, assignments)
        if sat:
            return assignments
    return None
