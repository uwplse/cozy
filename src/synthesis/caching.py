import os
import pickle
import sqlite3

from target_syntax import *
from syntax_tools import implies, equal, free_vars, subst
from solver import valid

CACHE_FILE = "/tmp/cozy-cache.pickle"

def load_cache():
    try:
        with open(CACHE_FILE, "rb") as f:
            return pickle.load(f)
    except FileNotFoundError:
        return []

def save_cache(data):
    print(" -> caching {}".format(repr(data)))
    tmp_file = CACHE_FILE + ".tmp"
    with open(tmp_file, "wb") as f:
        pickle.dump(data, f)
    os.rename(tmp_file, CACHE_FILE)

def find_cached_result(state_vars, assumptions, q, **opts):
    data = load_cache()
    print(" -> loaded {}".format(data))
    for res in data:
        (state_var, state_exp, new_q) = res
        if new_q.ret.type != q.ret.type:
            continue
        types1 = { v.id : v.type for v in free_vars(q.ret) }
        types2 = { v.id : v.type for v in free_vars(new_q.ret) }
        vc = subst(implies(EAll(assumptions), equal(q.ret, new_q.ret)), {state_var.id: state_exp})
        if not all(types1.get(v.id, v.type) == types2.get(v.id, v.type) for v in free_vars(vc)):
            continue
        if len(q.args) != len(new_q.args) or any(t1 != t2 for ((a1, t1), (a2, t2)) in zip(q.args, new_q.args)):
            continue
        vc = subst(vc, { a1: EVar(a2).with_type(t) for ((a1, _), (a2, t)) in zip(q.args, new_q.args) })
        print("considering {}".format(new_q))
        if valid(vc, **opts):
            return res
        else:
            print(" -> cache rejected {}".format(res))
    return None

def cache(key, res):
    data = load_cache()
    data.append(res)
    save_cache(data)
    new_data = load_cache()
    assert new_data == data, "loaded {}, expected {}".format(new_data, data)
