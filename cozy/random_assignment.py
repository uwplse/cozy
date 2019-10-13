import random
import string
from itertools import product

from cozy.common import FrozenDict
from cozy.syntax import *
from cozy.syntax_tools import free_vars
from cozy.evaluation import eval

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

def satisfy(e):
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