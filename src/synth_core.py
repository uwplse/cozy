from collections import defaultdict
import datetime
import sys

from target_syntax import *
from syntax_tools import subst, pprint, free_vars
from common import Visitor, fresh_name, declare_case, typechecked
from solver import satisfy, feasible
from evaluation import HoleException, eval, all_envs_for_hole

# Holes for synthesized expressions
EHole = declare_case(Exp, "EHole", ["name", "type", "builder"])

# Helpers
INT = TInt()
BOOL = TBool()

def cross_product(iters, i=0):
    if i == len(iters):
        yield ()
    if i >= len(iters):
        return
    for x in iters[i]:
        for rest in cross_product(iters, i + 1):
            yield (x,) + rest

class Builder(object):
    def __init__(self, roots, type_roots):
        self.roots = roots
        self.type_roots = type_roots

    @typechecked
    def enum_types(self, size : int, allow_collections : bool = True):
        if size <= 0:
            return
        elif size == 1:
            yield from self.type_roots
        else:
            if allow_collections:
                for t in self.enum_types(size - 1):
                    yield TBag(t)
                for (ksize, vsize) in pick_to_sum(2, size - 1):
                    for k in self.enum_types(ksize, allow_collections=False):
                        for v in self.enum_types(vsize):
                            yield TMap(k, v)
            for tuple_len in range(2, size):
                for sizes in pick_to_sum(tuple_len, size - 1):
                    gens = tuple(self.enum_types(sz, allow_collections=allow_collections) for sz in sizes)
                    for types in cross_product(gens):
                        yield TTuple(types)

    def build(self, cache, size):
        if size == 1:
            # for r in self.roots:
            #     print(" {} : {};".format(pprint(r), pprint(r.type)), end="")
            # print()
            yield from self.roots
            return
        for e in cache.find(type=TRecord, size=size-1):
            for (f,t) in e.type.fields:
                yield EGetField(e, f).with_type(t)
        for e in cache.find(type=TBag(INT), size=size-1):
            yield EUnaryOp("sum", e).with_type(INT)
        for e in cache.find(type=THandle, size=size-1):
            yield EGetField(e, "val").with_type(e.type.value_type)

        for (sz1, sz2) in pick_to_sum(2, size - 1):
            for a1 in cache.find(type=INT, size=sz1):
                for a2 in cache.find(type=INT, size=sz2):
                    yield EBinOp(a1, "+", a2).with_type(INT)
            for a1 in cache.find(size=sz1):
                for a2 in cache.find(type=a1.type, size=sz2):
                    yield EBinOp(a1, "==", a2).with_type(BOOL)
            for m in cache.find(type=TMap, size=sz1):
                for k in cache.find(type=m.type.k, size=sz2):
                    yield EMapGet(m, k).with_type(m.type.v)
            for bag in cache.find(type=TBag, size=sz2):
                    e = EVar(fresh_name()).with_type(bag.type.t)
                    for t in self.enum_types(sz1):
                        if not isinstance(bag, EMap):
                            hole = EHole(fresh_name(), t, self.with_roots([e]))
                            yield EMap(bag, ELambda(e, hole)).with_type(TBag(t))

        for bag in cache.find(type=TBag, size=size-1):
            e = EVar(fresh_name()).with_type(bag.type.t)
            if not isinstance(bag, EMap) and not isinstance(bag, EFilter):
                hole = EHole(fresh_name(), BOOL, self.with_roots([e]))
                yield EFilter(bag, ELambda(e, hole)).with_type(bag.type)

        for (bagsize, ksize, vsize) in pick_to_sum(3, size - 1):
            for kt in self.enum_types(ksize, allow_collections=False):
                for vt in self.enum_types(vsize):
                    for bag in cache.find(type=TBag, size=bagsize):
                        e = EVar(fresh_name()).with_type(bag.type.t)
                        es = EVar(fresh_name()).with_type(bag.type)
                        khole = EHole(fresh_name(), kt, self.with_roots([e]))
                        vhole = EHole(fresh_name(), vt, self.with_roots([es]))
                        yield EMakeMap(bag, ELambda(e, khole), ELambda(es, vhole)).with_type(TMap(kt, vt))
    def with_roots(self, new_roots):
        return Builder(list(new_roots) + list(self.roots), self.type_roots)

class Counterexample(Exception):
    def __init__(self, value):
        self.value = value

def find_subgoals(e):
    """
    Yields subgoals in evaluation order
    """
    class V(Visitor):
        def visit_EVar(self, e):
            return ()
        def visit_ENum(self, e):
            return ()
        def visit_EBool(self, e):
            return ()
        def visit_EEnumEntry(self, e):
            return ()
        def visit_EUnaryOp(self, e):
            return self.visit(e.e)
        def visit_EBinOp(self, e):
            yield from self.visit(e.e1)
            yield from self.visit(e.e2)
        def visit_ETuple(self, e):
            for ee in e.es:
                yield from self.visit(ee)
        def visit_EHole(self, e):
            yield (e.name, e.type, e.builder)
        def visit_EListComprehension(self, e):
            for clause in e.clauses:
                yield from self.visit(clause)
            yield from self.visit(e.e)
        def visit_CPull(self, e):
            return self.visit(e.e)
        def visit_CCond(self, e):
            return self.visit(e.e)
        def visit_EGetField(self, e):
            return self.visit(e.e)
        def visit_EMap(self, e):
            yield from self.visit(e.e)
            yield from self.visit(e.f)
        def visit_EFilter(self, e):
            yield from self.visit(e.e)
            yield from self.visit(e.p)
        def visit_EApp(self, e):
            yield from self.visit(e.arg)
            yield from self.visit(e.f)
        def visit_EMakeMap(self, e):
            yield from self.visit(e.e)
            yield from self.visit(e.key)
            yield from self.visit(e.value)
        def visit_EMapGet(self, e):
            yield from self.visit(e.map)
            yield from self.visit(e.key)
        def visit_ELambda(self, e):
            return self.visit(e.body)
        def visit_Exp(self, e):
            raise NotImplementedError("find_subgoals({})".format(e))
        def visit_object(self, o):
            raise Exception("cannot find subgoals in {}".format(repr(o)))
    return V().visit(e)

def contains_holes(e):
    for g in find_subgoals(e):
        return True
    return False

def pick_to_sum(n, total_size):
    if n == 0:
        assert total_size == 0, "total size is {}".format(total_size)
        yield ()
        return
    if n == 1:
        yield (total_size,)
        return
    for size in range(1, total_size - n + 2):
        for rest in pick_to_sum(n - 1, total_size - size):
            yield (size,) + rest

def pick(caches, types, sizes):
    if len(caches) == 0:
        yield ()
    else:
        for e in caches[0].find(type=types[0], size=sizes[0]):
            for es in pick(caches[1:], types[1:], sizes[1:]):
                yield (e,) + es

def nested_dict(n, t):
    if n <= 0:
        return t()
    return defaultdict(lambda: nested_dict(n-1, t))

class Cache(object):
    def __init__(self):
        self.data = nested_dict(3, list) # data[type_tag][type][size] is list of exprs
        self.seen = set()
    def tag(self, t):
        return type(t)
    def is_tag(self, t):
        return isinstance(t, type)
    def add(self, e, size):
        self.data[self.tag(e.type)][e.type][size].append(e)
    def find(self, type=None, size=None):
        type_tag = None
        if self.is_tag(type):
            type_tag = type
            type = None
        res = []
        for x in (self.data.values() if type_tag is None else [self.data.get(type_tag, {})]):
            for y in (x.values() if type is None else [x.get(type, {})]):
                for z in (y.values() if size is None else [y.get(size, [])]):
                    res += z
        return res

def distinct_exps(builder, examples, size, type):
    cache = Cache()
    seen = set()
    def fingerprint(e):
        return (e.type,) + tuple(eval(e, ex) for ex in examples)
    for i in range(size + 1):
        # if not cache.find(size=i):
        for e in builder.build(cache, i):
            if contains_holes(e):
                cache.add(e, size=i)
                continue
            fp = fingerprint(e)
            # print("fp({}) = {}".format(pprint(e), fp))
            if fp not in seen:
                seen.add(fp)
                cache.add(e, size=i)
    return cache.find(type=type, size=size)

def pick_goal(spec, examples):
    # assert contains_holes(spec), "no subgoals in {}".format(spec)
    # scores = defaultdict(int)
    # for ex in examples:
    #     try:
    #         eval(spec, ex)
    #     except HoleException as e:
    #         scores[e.hole.name] += 1
    # if not scores:
    #     for g in find_subgoals(spec):
    #         return g[0]
    # return max(scores.keys(), key=scores.get)
    for g in find_subgoals(spec):
        return g[0]
    assert False, "no subgoals in {}".format(spec)

def construct_inputs(spec, goal_name, examples):
    for ex in examples:
        yield from all_envs_for_hole(spec, ex, goal_name)

def find_consistent_exps(
        spec     : Exp,
        examples : [Exp],
        size     : int = None,
        cache    : Cache = None,
        seen     : set = None):

    indent = ""

    if cache is None:
        cache = Cache()
    if seen is None:
        seen = set()

    # print("{}find({}, {})".format(indent, pprint(spec), size))

    goals = list(find_subgoals(spec))

    if not goals:
        if size == 0 and all(eval(spec, ex) for ex in examples):
            print("final: {}".format(pprint(spec)))
            yield { }
        else:
            if size != 0:
                # print("REJECTED (wrong size): {}".format(pprint(spec)))
                pass
            else:
                print("  REJECTED: {} [examples={}]".format(pprint(spec), examples))
            pass
        return

    if size is None:
        size = 1
        while True:
            print("size={}".format(size))
            yield from find_consistent_exps(spec, examples, size, cache=cache, seen=seen)
            size += 1
        return

    # not strictly necessary, but this helps
    if len(goals) > size:
        return

    name = pick_goal(spec, examples)
    _, type, builder = [goal for goal in goals if goal[0] == name][0]
    goals = [goal for goal in goals if goal[0] != name]
    g_examples = list(construct_inputs(spec, name, examples))

    # print("{}##### working on {}".format(indent, name))
    for (sz1, sz2) in pick_to_sum(2, size + 1):
        sz2 -= 1
        # print("{}({},{})".format(indent, sz1, sz2))
        for e in distinct_exps(builder, g_examples, size=sz1, type=type):
            # print("{}| considering {} for {} [examples={}]".format(indent, pprint(e), name, g_examples))
            spec2 = subst(spec, { name : e })
            if not feasible(spec2, examples):
                print("{}INFEASIBLE: {}".format(indent, pprint(spec2)))
                continue
            for d in find_consistent_exps(spec2, examples, sz2, cache=cache, seen=seen):
                # TODO: double-check consistency
                if d is not None:
                    d[name] = e
                yield d

def expand(e, mapping):
    while contains_holes(e):
        prev = e
        e = subst(e, mapping)
        assert e != prev, "failed to converge: {}, {}".format(new_spec, mapping)
    return e

def synth(spec):
    examples = []
    while True:
        for mapping in find_consistent_exps(spec, examples):
            new_spec = expand(spec, mapping)

            print("considering: {}".format(pprint(new_spec)))
            if all(eval(new_spec, ex) for ex in examples):
                model = satisfy(EUnaryOp("not", new_spec).with_type(TBool()))
                if model is not None:
                    assert model not in examples, "got duplicate example: {}; examples={}".format(model, examples)
                    print("new example: {}".format(model))
                    examples.append(model)
                    break
                else:
                    yield mapping
            else:
                assert False
                print("rejected: {}".format(pprint(new_spec)))

if __name__ == "__main__":
    # Next steps:
    #   - find a way to bias towards the right answer

    INT = TInt()
    LONG = TLong()
    BOOL = TBool()
    REC = TRecord((("key", INT), ("value", INT)))
    bag = EVar("bag").with_type(TBag(REC))
    v = EVar("x").with_type(REC)
    arg = EVar("k").with_type(INT)
    target = EUnaryOp("sum", EListComprehension(EGetField(v, "value"), (CPull(v.id, bag), CCond(EBinOp(EGetField(v, "key"), "==", arg))))).with_type(INT)

    if False:
        query_hole = EHole("query", target.type, Builder(free_vars(target)))
        spec = EBinOp(query_hole, "==", target)
    else:
        state_var = EVar(fresh_name("state")).with_type(TMap(INT, INT))
        state_hole = EHole("state", state_var.type, Builder([bag]))
        query_hole = EHole("query", target.type, Builder([state_var, arg]))
        spec = EBinOp(EApp(ELambda(state_var, query_hole), state_hole), "==", target)

    for mapping in synth(spec):
        result = expand(query_hole, mapping)
        print(pprint(result))
        break
