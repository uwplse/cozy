import random
import string

from cozy.common import FrozenDict
from cozy.syntax import TBag, TInt, TString, ENum, EStr, TRecord, ESingleton, EMakeRecord
from cozy.syntax_tools import free_vars
from cozy.syntax_tools import pprint
from cozy.evaluation import eval, uneval

# FIXME: how to use solver for this purpose?
from cozy.value_types import Bag


def construct_random_value(t):
    if isinstance(t, TBag):
        return Bag((construct_random_value(t.elem_type),))
    if isinstance(t, TInt):
        return random.randint(0, 100)
    if isinstance(t, TString):
        return ''.join(random.choice(string.ascii_letters) for _ in range(8))
    if isinstance(t, TRecord):
        return FrozenDict({ name : construct_random_value(ty) for name, ty in t.fields })
    raise Exception("Unknown type for random value construction: {}".format(t))
#
# def reconstruct(e):
#     if isinstance(e, ESingleton):
#         return [reconstruct(e.e)]
#     if isinstance(e, EMakeRecord):
#         return { id : reconstruct(val) for id, val in e.fields }
#     return e

def find_counterexample(e):
    assignments = {}
    assignments_reconstructed = {}
    for v in free_vars(e):
        val = construct_random_value(v.type)
        assignments[v.id] = val
        # assignments_reconstructed[v.id] = reconstruct(val)
    sat = eval(e, assignments)
    if not sat:
        return assignments
    return None