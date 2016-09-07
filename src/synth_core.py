from collections import namedtuple, deque, defaultdict
import datetime
import sys

from target_syntax import *
from syntax_tools import subst, pprint, free_vars
from common import Visitor, fresh_name, declare_case, typechecked
from solver import satisfy
from evaluation import HoleException, eval, all_envs_for_hole

# Holes for synthesized expressions
EHole = declare_case(Exp, "EHole", ["name", "type", "builder"])

class Builder(object):
    def __init__(self, roots):
        self.roots = roots
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
        for (sz1, sz2) in pick_to_sum(2, size - 1):
            for a1 in cache.find(type=INT, size=sz1):
                for a2 in cache.find(type=INT, size=sz2):
                    yield EBinOp(a1, "+", a2).with_type(INT)
            for m in cache.find(type=TMap, size=sz1):
                for k in cache.find(type=m.type.k, size=sz2):
                    yield EMapGet(m, k).with_type(m.type.v)
            for t in enum_types(sz1):
                for bag in cache.find(type=TBag, size=sz2):
                    if not isinstance(bag, EMap):
                        e = EVar(fresh_name()).with_type(bag.type.t)
                        hole = EHole(fresh_name(), t, self.with_roots([e]))
                        yield EMap(bag, ELambda(e, hole)).with_type(TBag(t))
        for (bagsize, ksize, vsize) in pick_to_sum(3, size - 1):
            for kt in enum_types(ksize):
                for vt in enum_types(vsize):
                    for bag in cache.find(type=TBag, size=bagsize):
                        e = EVar(fresh_name()).with_type(bag.type.t)
                        es = EVar(fresh_name()).with_type(bag.type)
                        khole = EHole(fresh_name(), kt, self.with_roots([e]))
                        vhole = EHole(fresh_name(), vt, self.with_roots([es]))
                        yield EMakeMap(bag, ELambda(e, khole), ELambda(es, vhole)).with_type(TMap(kt, vt))
    def with_roots(self, new_roots):
        return Builder(list(new_roots) + list(self.roots))

class Counterexample(Exception):
    def __init__(self, value):
        self.value = value

def find_subgoals(e):
    class V(Visitor):
        def visit_EVar(self, e):
            return ()
        def visit_ENum(self, e):
            return ()
        def visit_EUnaryOp(self, e):
            return self.visit(e.e)
        def visit_EBinOp(self, e):
            yield from self.visit(e.e1)
            yield from self.visit(e.e2)
        def visit_EHole(self, e):
            yield (e.name, e.type, e.builder)
        def visit_EListComprehension(self, e):
            yield from self.visit(e.e)
            for clause in e.clauses:
                yield from self.visit(clause)
        def visit_CPull(self, e):
            return self.visit(e.e)
        def visit_CCond(self, e):
            return self.visit(e.e)
        def visit_EGetField(self, e):
            return self.visit(e.e)
        def visit_EMap(self, e):
            yield from self.visit(e.e)
            yield from self.visit(e.f)
        def visit_EApp(self, e):
            yield from self.visit(e.f)
            yield from self.visit(e.arg)
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

Solution = namedtuple("Solution", ["exps"])
PartialSolution = namedtuple("PartialSolution", ["examples", "spec", "k"])

@typechecked
def enum_types(size : int):
    if size <= 0:
        return
    elif size == 1:
        yield TInt()
        yield TBool()
    else:
        for t in enum_types(size - 1):
            yield TBag(t)
        for k in enum_types(1):
            for v in enum_types(size - 2):
                yield TMap(k, v)
                # TODO: allow record types as map keys

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
    assert contains_holes(spec), "no subgoals in {}".format(spec)
    scores = defaultdict(int)
    for ex in examples:
        try:
            eval(spec, ex)
        except HoleException as e:
            scores[e.hole.name] += 1
    if not scores:
        for g in find_subgoals(spec):
            return g[0]
    return max(scores.keys(), key=scores.get)

def construct_inputs(spec, goal_name, examples):
    for ex in examples:
        yield from all_envs_for_hole(spec, ex, goal_name)

def find_consistent_exps(
        spec     : Exp,
        examples : [Exp],
        size     : int = None,
        cache    : Cache = None,
        seen     : set = None):

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
            # if size != 0:
            #     # print("REJECTED (wrong size): {}".format(pprint(spec)))
            #     pass
            # else:
            #     print("  REJECTED: {} [examples={}]".format(pprint(spec), examples))
            pass
        return

    if size is None:
        size = 1
        while True:
            # print("size={}".format(size))
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

    # print("{}#####".format(indent))
    for (sz1, sz2) in pick_to_sum(2, size + 1):
        yield
        sz2 -= 1
        # print("{}({},{})".format(indent, sz1, sz2))
        for e in distinct_exps(builder, g_examples, size=sz1, type=type):
            # print("{}| considering {} for {} [examples={}]".format(indent, pprint(e), name, g_examples))
            for d in find_consistent_exps(subst(spec, { name : e }), examples, sz2, cache=cache, seen=seen):
                # TODO: double-check consistency
                if d is not None:
                    d[name] = e
                yield d

def synth(spec):
    examples = []
    while True:
        for mapping in find_consistent_exps(spec, examples):
            if mapping is None:
                yield
                continue

            new_spec = spec
            while contains_holes(new_spec):
                prev_spec = new_spec
                new_spec = subst(new_spec, mapping)
                assert new_spec != prev_spec, "failed to converge: {}, {}".format(new_spec, mapping)

            print("considering: {}".format(pprint(new_spec)))
            if all(eval(new_spec, ex) for ex in examples):
                model = satisfy(EUnaryOp("not", new_spec).with_type(TBool()))
                if model is not None:
                    print("new example: {}".format(model))
                    examples.append(model)
                    yield
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

    query_hole = EHole("query", target.type, Builder(free_vars(target)))
    spec = EBinOp(query_hole, "==", target)

    for mapping in synth(spec):
        if mapping is not None:

            result = query_hole
            while contains_holes(result):
                prev_result = result
                result = subst(result, mapping)
                assert result != prev_result, "failed to converge: {}, {}".format(result, mapping)

            print(pprint(result))
            break
