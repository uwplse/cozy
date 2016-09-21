from collections import defaultdict
import datetime
import itertools
import sys

from target_syntax import *
from typecheck import INT, BOOL
from syntax_tools import subst, pprint, free_vars, BottomUpExplorer
from common import Visitor, fresh_name, declare_case, typechecked, unique
from solver import satisfy, feasible
from evaluation import HoleException, eval, all_envs_for_hole

# Holes for synthesized expressions
EHole = declare_case(Exp, "EHole", ["name", "type", "builder"])

def cross_product(iters, i=0):
    if i == len(iters):
        yield ()
    if i >= len(iters):
        return
    for x in iters[i]:
        for rest in cross_product(iters, i + 1):
            yield (x,) + rest

class Cache(object):
    def __init__(self):
        self.data = nested_dict(3, list) # data[type_tag][type][size] is list of exprs
        self.size = 0
    def tag(self, t):
        return type(t)
    def is_tag(self, t):
        return isinstance(t, type)
    def add(self, e, size):
        self.data[self.tag(e.type)][e.type][size].append(e)
        self.size += 1
    def find(self, type=None, size=None):
        type_tag = None
        if type is not None:
            if self.is_tag(type):
                type_tag = type
                type = None
            else:
                type_tag = self.tag(type)
        res = []
        for x in (self.data.values() if type_tag is None else [self.data.get(type_tag, {})]):
            for y in (x.values() if type is None else [x.get(type, {})]):
                for z in (y.values() if size is None else [y.get(size, [])]):
                    res += z
        return res
    def __len__(self):
        return self.size

class Builder(object):
    def __init__(self, roots, type_roots):
        self.roots = roots
        self.type_roots = type_roots
        self.build_maps = True
        self.build_tuples = True

    @typechecked
    def enum_types(
            self,
            size          : int,
            allow_bags    : bool = True,
            allow_maps    : bool = True,
            allow_tuples  : bool = True,
            max_bag_depth : int  = 2):
        if size <= 0:
            return
        elif size == 1:
            yield from self.type_roots
        else:
            if allow_bags and max_bag_depth > 0:
                for t in self.enum_types(size - 1, allow_maps=allow_maps, allow_tuples=allow_tuples, max_bag_depth=max_bag_depth-1):
                    yield TBag(t)
            if allow_maps:
                for (ksize, vsize) in pick_to_sum(2, size - 1):
                    for k in self.enum_types(ksize, allow_bags=False, allow_maps=False, allow_tuples=allow_tuples):
                        for v in self.enum_types(vsize, allow_bags=allow_bags, allow_maps=False, allow_tuples=allow_tuples, max_bag_depth=max_bag_depth):
                            yield TMap(k, v)
            if allow_tuples:
                for tuple_len in range(2, size):
                    for sizes in pick_to_sum(tuple_len, size - 1):
                        gens = tuple(list(self.enum_types(sz, allow_bags=allow_bags, allow_maps=allow_maps, allow_tuples=False, max_bag_depth=max_bag_depth)) for sz in sizes)
                        for types in cross_product(gens):
                            yield TTuple(types)

    def instantiate(self, e : Exp, cache : Cache, total_size : int):
        holes = list(find_holes(e))
        if not holes:
            yield e
            return
        for sizes in pick_to_sum(len(holes), total_size):
            exp_lists = tuple(list(cache.find(type=hole.type, size=sz)) for (hole, sz) in zip(holes, sizes))
            for exps in cross_product(exp_lists):
                # print("exps:  {}".format(", ".join([pprint(e) for e in exps])))
                # print("types: {}".format(", ".join([pprint(e.type) for e in exps])))
                remap = { hole.name : e for (hole, e) in zip(holes, exps) }
                res = subst(e, remap)
                # print(pprint(e) + " ----> " + pprint(res))
                yield res

    def build(self, cache, size):
        if size == 1:
            # for r in self.roots:
            #     print(" {} : {};".format(pprint(r), pprint(r.type)), end="")
            # print()
            for r in self.roots:
                if not contains_holes(r):
                    yield r
            return

        for r in self.roots:
            if contains_holes(r):
                yield from self.instantiate(r, cache, size - 1)

        # for e in cache.find(type=TRecord, size=size-1):
        #     for (f,t) in e.type.fields:
        #         yield EGetField(e, f).with_type(t)
        for e in cache.find(type=TBag(INT), size=size-1):
            yield EUnaryOp("sum", e).with_type(INT)
        for e in cache.find(type=THandle, size=size-1):
            yield EGetField(e, "val").with_type(e.type.value_type)
        for e in cache.find(type=TTuple, size=size-1):
            for n in range(len(e.type.ts)):
                yield ETupleGet(e, n).with_type(e.type.ts[n])

        for (sz1, sz2) in pick_to_sum(2, size - 1):
            for a1 in cache.find(type=INT, size=sz1):
                for a2 in cache.find(type=INT, size=sz2):
                    yield EBinOp(a1, "+", a2).with_type(INT)
            for a1 in cache.find(size=sz1):
                if not isinstance(a1.type, TMap):
                    for a2 in cache.find(type=a1.type, size=sz2):
                        yield EBinOp(a1, "==", a2).with_type(BOOL)
            for m in cache.find(type=TMap, size=sz1):
                for k in cache.find(type=m.type.k, size=sz2):
                    yield EMapGet(m, k).with_type(m.type.v)

        for r in self.roots:
            for hole in find_holes(r):
                for (sz1, sz2) in pick_to_sum(2, size - 1):
                    for bag in cache.find(type=TBag(hole.type), size=sz1):
                        map_arg = EVar(fresh_name()).with_type(hole.type)
                        for body in self.instantiate(subst(r, { hole.name: map_arg }), cache, sz2):
                            e = EMap(bag, ELambda(map_arg, body)).with_type(TBag(r.type))
                            # print("filter: {}".format(pprint(e)))
                            yield e

        for r in self.roots:
            if r.type == BOOL:
                for hole in find_holes(r):
                    for (sz1, sz2) in pick_to_sum(2, size - 1):
                        for bag in cache.find(type=TBag(hole.type), size=sz1):
                            filt_arg = EVar(fresh_name()).with_type(hole.type)
                            for body in self.instantiate(subst(r, { hole.name: filt_arg }), cache, sz2):
                                e = EFilter(bag, ELambda(filt_arg, body)).with_type(bag.type)
                                # print("filter: {}".format(pprint(e)))
                                yield e

        # if self.build_tuples:
        #     for tuple_len in range(2, size):
        #         for sizes in pick_to_sum(tuple_len, size - 1):
        #             exp_lists = tuple(list(cache.find(size=sz)) for sz in sizes)
        #             for exps in cross_product(exp_lists):
        #                 e = ETuple(exps).with_type(TTuple(tuple(e.type for e in exps)))
        #                 # if size == 3 and e.type == TTuple((INT, INT)): print(pprint(e))
        #                 yield e

        # if self.build_maps:
        #     for (bagsize, ksize, vsize) in pick_to_sum(3, size - 1):
        #         for kt in self.enum_types(ksize, allow_bags=False, allow_maps=False):
        #             for vt in self.enum_types(vsize, allow_maps=False):
        #                 for bag in cache.find(type=TBag, size=bagsize):
        #                     if isinstance(bag, EMap):
        #                         continue
        #                     e = EVar(fresh_name()).with_type(bag.type.t)
        #                     es = EVar(fresh_name()).with_type(bag.type)
        #                     khole = EHole(fresh_name(), kt, self.with_roots([e], build_maps=False))
        #                     vhole = EHole(fresh_name(), vt, self.with_roots([es], build_maps=False))
        #                     yield EMakeMap(bag, ELambda(e, khole), ELambda(es, vhole)).with_type(TMap(kt, vt))
    def with_roots(self, new_roots, build_maps=True):
        b = Builder(list(new_roots) + list(self.roots), self.type_roots)
        b.build_maps = self.build_maps and build_maps
        b.build_tuples = self.build_tuples
        return b

class Counterexample(Exception):
    def __init__(self, value):
        self.value = value

def find_holes(e):
    """
    Yields holes in evaluation order
    """
    class V(BottomUpExplorer):
        def visit_EHole(self, e):
            return (e,)
        def visit_EApp(self, e):
            """
            An application node has children (function, arg), but the arg is
            evaluated first so we need to special-case this and reverse the
            exploration order.
            """
            return itertools.chain(
                self.visit(e.arg),
                self.visit(e.f))
        def join(self, x, children):
            return itertools.chain(*children)
    return unique(V().visit(e), key=lambda g: g.name)

def contains_holes(e):
    for g in find_holes(e):
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

# def distinct_exps(builder, examples, size, type):
#     cache = Cache()
#     seen = set()
#     def fingerprint(e):
#         return (e.type,) + tuple(eval(e, ex) for ex in examples)
#     for i in range(size + 1):
#         # if not cache.find(size=i):
#         for e in builder.build(cache, i):
#             if contains_holes(e):
#                 cache.add(e, size=i)
#                 continue
#             fp = fingerprint(e)
#             # print("fp({}) = {}".format(pprint(e), fp))
#             if fp not in seen:
#                 seen.add(fp)
#                 cache.add(e, size=i)
#                 # print("    ---> adding @ size={}".format(i))
#     # print("RESULT={}".format(list(cache.find(type=type, size=size))))
#     return cache.find(type=type, size=size)

def pick_goal(spec, examples):
    # assert contains_holes(spec), "no subgoals in {}".format(spec)
    # scores = defaultdict(int)
    # for ex in examples:
    #     try:
    #         eval(spec, ex)
    #     except HoleException as e:
    #         scores[e.hole.name] += 1
    # if not scores:
    #     for g in find_holes(spec):
    #         return g[0]
    # return max(scores.keys(), key=scores.get)
    for g in find_holes(spec):
        return g.name
    assert False, "no subgoals in {}".format(spec)

def construct_inputs(spec, goal_name, examples):
    for ex in examples:
        yield from all_envs_for_hole(spec, ex, goal_name)

indent = ""
def find_consistent_exps(
        spec     : Exp,
        examples : [Exp],
        size     : int = None):

    global indent
    indent = indent + "  "

    try:

        # print("{}find({}, {})".format(indent, pprint(spec), size))

        goals = list(find_holes(spec))

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
                print("size={}".format(size))
                yield from find_consistent_exps(spec, examples, size)
                size += 1
            return

        # not strictly necessary, but this helps
        if len(goals) > size:
            return

        name = pick_goal(spec, examples)
        g = [goal for goal in goals if goal.name == name][0]
        type = g.type
        builder = g.builder
        goals = [goal for goal in goals if goal.name != name]
        g_examples = list(construct_inputs(spec, name, examples))

        # print("{}##### working on {}".format(indent, name))
        cache = Cache()
        seen = set()
        for sz1 in range(1, size + 1):
            sz2 = size - sz1
        # for (sz1, sz2) in pick_to_sum(2, size + 1):
        #     sz2 -= 1
            # print("{}({},{})".format(indent, sz1, sz2))
            found = False
            def fingerprint(e):
                return (e.type,) + tuple(eval(e, ex) for ex in g_examples)
            for e in builder.build(cache, sz1):
                if contains_holes(e):
                    cache.add(e, size=sz1)
                else:
                    fp = fingerprint(e)
                    if fp not in seen:
                        seen.add(fp)
                        cache.add(e, size=sz1)
                    else:
                        continue
                if e.type != type:
                    continue
            # for e in distinct_exps(builder, g_examples, size=sz1, type=type):
                # print("{}| considering {} for {} [examples={}]".format(indent, pprint(e), name, g_examples))
                spec2 = subst(spec, { name : e })
                # print("{}|{} ---> {}".format(indent, name, pprint(e)))
                # print("{}|{}".format(indent, pprint(spec)))
                # print("{}|{}".format(indent, pprint(spec2)))
                assert name not in (g.name for g in find_holes(spec2))
                if not feasible(spec2, examples):
                    print("{}INFEASIBLE: {}".format(indent, pprint(spec2)))
                    continue
                for d in find_consistent_exps(spec2, examples, sz2):
                    # TODO: double-check consistency
                    if d is not None:
                        d[name] = e
                    found = True
                    yield d
            # if not found:
            #     print("{}none of size {} while synth'ing {} + {}".format(indent, sz1, name, list(g.name for g in goals)))
                # if sz1 == 1:
                #     print("{}roots of builder are: {}".format(indent, ", ".join("{}:{}".format(pprint(e), pprint(e.type)) for e in builder.roots)))
        # print("{}-> for {}: cache size = {}".format(indent, name, len(cache)))
    finally:
        indent = indent[2:]

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
