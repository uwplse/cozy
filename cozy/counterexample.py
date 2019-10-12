import random
import string
from itertools import product

from cozy.common import FrozenDict
from cozy.syntax import TBag, TInt, TString, ENum, EStr, TRecord, ESingleton, EMakeRecord
from cozy.syntax_tools import free_vars
from cozy.syntax_tools import pprint
from cozy.evaluation import eval, uneval

# FIXME: how to use solver for this purpose?
from cozy.value_types import Bag

def random_value(t):
    if isinstance(t, TBag):
        for v in random_value(t.elem_type):
            yield Bag((v,))
    elif isinstance(t, TInt):
        yield random.randint(0, 100)
    elif isinstance(t, TString):
        yield ''.join(random.choice(string.ascii_letters) for _ in range(8))
    elif isinstance(t, TRecord):
        iterables = [ random_value(ty) for _, ty in t.fields ]
        for vs in product(*iterables):
            yield FrozenDict({ field[0] : v for v, field in zip(vs, t.fields) })
    else:
        raise Exception("Unknown type for random value construction: {}".format(t))
#
# def reconstruct(e):
#     if isinstance(e, ESingleton):
#         return [reconstruct(e.e)]
#     if isinstance(e, EMakeRecord):
#         return { id : reconstruct(val) for id, val in e.fields }
#     return e

def find_counterexample(e):
    assignments_reconstructed = {}
    iterables = [ random_value(v.type) for v in free_vars(e) ]
    ids = [ v.id for v in free_vars(e) ]
    for vs in product(*iterables):
        assignments = {}
        for id, val in zip(ids, vs):
            assignments[id] = val
        # assignments_reconstructed[v.id] = reconstruct(val)
        print("[DEBUG]: assignments: %s" % assignments)
        sat = eval(e, assignments)
        if not sat:
            return assignments
    return None