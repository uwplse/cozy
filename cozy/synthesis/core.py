from collections import defaultdict
import datetime
import itertools
import sys

from cozy.target_syntax import *
from cozy.typecheck import INT, BOOL
from cozy.syntax_tools import subst, pprint, free_vars, BottomUpExplorer, equal, fresh_var
from cozy.common import Visitor, fresh_name, typechecked, unique, pick_to_sum, cross_product
from cozy.solver import satisfy, feasible
from cozy.evaluation import HoleException, eval, all_envs_for_hole
from cozy.timeouts import Timeout

class Cache(object):
    def __init__(self, items=None):
        self.data = nested_dict(3, list) # data[type_tag][type][size] is list of exprs
        self.size = 0
        if items:
            for (e, size) in items:
                self.add(e, size)
    def tag(self, t):
        return type(t)
    def is_tag(self, t):
        return isinstance(t, type)
    def add(self, e, size):
        self.data[self.tag(e.type)][e.type][size].append(e)
        self.size += 1
    def evict(self, e, size):
        self.data[self.tag(e.type)][e.type][size].remove(e)
        self.size -= 1
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
    def __iter__(self):
        for x in self.data.values():
            for y in x.values():
                for (size, es) in y.items():
                    for e in es:
                        yield (e, size)
    def __len__(self):
        return self.size

@typechecked
def instantiate(e : Exp, cache : Cache, total_size : int):
    holes = list(find_holes(e))
    if not holes:
        if total_size == 1:
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

class CostModel(object):
    def cost(self, e):
        assert not contains_holes(e)
        return self.best_case_cost(e)
    def best_case_cost(self, e):
        raise NotImplementedError()
    def is_monotonic(self):
        raise NotImplementedError()

class ConstantCost(CostModel):
    def best_case_cost(self, e):
        return 1
    def is_monotonic(self):
        return True

class CardinalityVisitor(BottomUpExplorer):
    def visit_EVar(self, v):
        return 1000
    def visit_EMakeMap(self, e):
        return self.visit(e.e)
    def visit_EMapGet(self, e):
        return self.visit(e.map) / 3
    def visit_EFilter(self, e):
        if e.p.body == EBool(True):
            return self.visit(e.e)
        if e.p.body == EBool(False):
            return 0
        return self.visit(e.e) / 2
    def visit_EBinOp(self, e):
        if e.op == "+":
            return self.visit(e.e1) + self.visit(e.e2)
        else:
            raise NotImplementedError(e.op)
    def visit_EMap(self, e):
        return self.visit(e.e)
    def visit_EFlatMap(self, e):
        return self.visit(e.e) * self.visit(e.f.body)
    def visit_Exp(self, e):
        return 0

cardinality = CardinalityVisitor().visit

class MemoryUsageCostModel(CostModel, BottomUpExplorer):
    def best_case_cost(self, e):
        try:
            return self.visit(e)
        except:
            print("estimating memory usage of {}".format(pprint(e)))
            raise
    def is_monotonic(self):
        return True

    def visit_EVar(self, e):
        if isinstance(e.type, TBag):
            return cardinality(e)
        return 1
    def visit_EUnaryOp(self, e):
        if e.op == "sum":
            return 1 # TODO: sizeof(int)
        if e.op == "not":
            return 1 # TODO: sizeof(bool)
        if e.op == "the":
            return 1 # TODO: sizeof(e.type)
        raise NotImplementedError(e.op)
    def visit_EBool(self, e):
        return 1 # TODO: sizeof(bool)
    def visit_EBinOp(self, e):
        return 1 # TODO: sizeof(e.type)
    def visit_EMap(self, e):
        return cardinality(e.e) * self.visit(e.f.body)
    def visit_EFlatMap(self, e):
        return cardinality(e.e) * self.visit(e.f.body)
    def visit_EFilter(self, e):
        return cardinality(e) # TODO: c * sizeof(e.type.t)
    def visit_EMakeMap(self, e):
        return cardinality(e.e) * (self.visit(e.key.body) + self.visit(e.value.body))
    def visit_EMapGet(self, e):
        assert isinstance(e.map, EMakeMap)
        return self.visit(e.map.value.apply_to(EFilter(e.map.e, ELambda(e.map.key.arg, equal(e.map.key.arg, fresh_var(e.map.key.arg.type))))))
    def visit_EAlterMaybe(self, e):
        return self.visit(e.f.body)
    def visit_EGetField(self, e):
        return 1 # TODO: sizeof(e.type)
    def visit_Exp(self, e):
        raise NotImplementedError(repr(e))

class RunTimeCostModel(CostModel, BottomUpExplorer):
    def best_case_cost(self, e):
        return self.visit(e)
    def is_monotonic(self):
        return True

    def visit_EVar(self, e):
        return 1
    def visit_EUnaryOp(self, e):
        cost = self.visit(e.e)
        if e.op == "sum":
            cost += cardinality(e.e)
        return cost
    def visit_EMap(self, e):
        return self.visit(e.e) + cardinality(e.e) * self.visit(e.f.body)
    def visit_EFlatMap(self, e):
        return self.visit(EFlatten(EMap(e.e, e.f)))
    def visit_EFilter(self, e):
        return self.visit(e.e) + cardinality(e.e) * self.visit(e.p.body)
    def visit_EMakeMap(self, e):
        return self.visit(e.e) + cardinality(e.e) * (self.visit(e.key.body) + self.visit(e.value.body))
    def join(self, x, child_costs):
        return 0.01 + sum(child_costs)

class ExpBuilder(object):
    def build(self, cache, size):
        raise NotImplementedError()
    def cost_model(self):
        return ConstantCost()

class Builder(ExpBuilder):
    def __init__(self, roots, build_sums = True, cost_model = ConstantCost()):
        self.roots = roots
        self.build_sums = build_sums
        self.cm = cost_model

    def cost_model(self):
        return self.cm

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
                yield from instantiate(r, cache, size - 1)

        for e in cache.find(type=TRecord, size=size-1):
            for (f,t) in e.type.fields:
                yield EGetField(e, f).with_type(t)
        if self.build_sums:
            for e in cache.find(type=TBag(INT), size=size-1):
                yield EUnaryOp("sum", e).with_type(INT)
        for e in cache.find(type=TBag, size=size-1):
            yield EUnaryOp("the", e).with_type(TMaybe(e.type.t))
        for e in cache.find(type=THandle, size=size-1):
            yield EGetField(e, "val").with_type(e.type.value_type)
        for e in cache.find(type=TTuple, size=size-1):
            for n in range(len(e.type.ts)):
                yield ETupleGet(e, n).with_type(e.type.ts[n])
        for e in cache.find(type=BOOL, size=size-1):
            yield EUnaryOp("not", e).with_type(BOOL)

        for (sz1, sz2) in pick_to_sum(2, size - 1):
            # for a1 in cache.find(type=INT, size=sz1):
            #     for a2 in cache.find(type=INT, size=sz2):
            #         yield EBinOp(a1, "+", a2).with_type(INT)
            for a1 in cache.find(type=TBag, size=sz1):
                for a2 in cache.find(type=a1.type, size=sz2):
                    yield EBinOp(a1, "+", a2).with_type(a1.type)
            for a1 in cache.find(type=BOOL, size=sz1):
                for a2 in cache.find(type=BOOL, size=sz2):
                    yield EBinOp(a1, "and", a2).with_type(BOOL)
                    yield EBinOp(a1, "or", a2).with_type(BOOL)
            for a1 in cache.find(size=sz1):
                if not isinstance(a1.type, TMap):
                    for a2 in cache.find(type=a1.type, size=sz2):
                        yield EBinOp(a1, "==", a2).with_type(BOOL)
            for m in cache.find(type=TMap, size=sz1):
                for k in cache.find(type=m.type.k, size=sz2):
                    yield EMapGet(m, k).with_type(m.type.v)

    def with_roots(self, new_roots):
        b = Builder(list(new_roots) + list(self.roots))
        b.build_sums = self.build_sums
        b.cm = self.cm
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

def ints(start, end):
    """
    Yields integers from the range [start, end]. If end is None, then it yields
    integers from the range [start, INFINITY).
    """
    i = start
    if end is None:
        while True:
            yield i
            i += 1
    else:
        yield from range(start, end + 1)

def values_of_type(value, value_type, desired_type):
    # see evaluation.mkval for info on the structure of values
    if value_type == desired_type:
        yield value
    elif isinstance(value_type, TBag):
        for x in value:
            yield from values_of_type(x, value_type.t, desired_type)
    else:
        # I think this is OK since all values for bound vars are pulled from
        # bags or other collections.
        pass

def instantiate_examples(examples, vars, binder):
    for e in examples:
        if binder.id in e:
            yield e
        for v in vars:
            for possible_value in unique(values_of_type(e[v.id], v.type, binder.type)):
                # print("possible value for {}: {}".format(pprint(binder.type), repr(possible_value)))
                e2 = dict(e)
                e2[binder.id] = possible_value
                yield e2

def fingerprint(e, examples, vars : {EVar}, binders : [EVar]):
    fvs = free_vars(e)
    for v in binders:
        examples = list(instantiate_examples(examples, vars, v))
        # print("augmented examples for {}: {}".format(v, examples))
    return (e.type,) + tuple(eval(e, ex) for ex in examples)

indent = ""
def find_consistent_exps(
        spec      : Exp,
        binders   : [EVar],
        examples  : [{str:object}],
        max_size  : int = None,
        best_cost : float = None,
        timeout   : Timeout = None):

    global indent
    indent = indent + "  "
    fvs = free_vars(spec)

    try:

        # print("{}find({}, {})".format(indent, pprint(spec), size))

        goals = list(find_holes(spec))

        if not goals:
            if max_size == 0 and all(eval(spec, ex) for ex in examples):
                print("final: {}".format(pprint(spec)))
                yield { }
            else:
                # if size != 0:
                #     print("REJECTED (wrong size): {}".format(pprint(spec)))
                # else:
                #     print("  REJECTED: {} [examples={}]".format(pprint(spec), examples))
                pass
            return

        # not strictly necessary, but this helps
        if max_size is not None and len(goals) > max_size:
            return

        name = pick_goal(spec, examples)
        g = [goal for goal in goals if goal.name == name][0]
        type = g.type
        builder = g.builder
        cost_model = builder.cost_model()
        goals = [goal for goal in goals if goal.name != name]
        g_examples = list(construct_inputs(spec, name, examples))

        # print("{}##### working on {}".format(indent, name))
        cache = Cache()
        seen = {} # maps fingerprints to (cost, exp, size)
        for size in ints(1, max_size):
            if max_size is None:
                print("size={}; |cache|={}".format(size, len(cache)))
            for sz1 in range(1, size + 1):
                if timeout is not None:
                    timeout.check()
                sz2 = size - sz1
            # for (sz1, sz2) in pick_to_sum(2, size + 1):
            #     sz2 -= 1
                # print("{}({},{})".format(indent, sz1, sz2))
                found = False
                for e in (builder.build(cache, sz1) if sz1 == size else cache.find(size=sz1)):
                    if contains_holes(e):
                        raise Exception()
                        if cost_model.is_monotonic() and best_cost is not None and cost_model.best_case_cost(e) > best_cost:
                            continue
                        cache.add(e, size=sz1)
                        continue

                    cost = cost_model.cost(e)

                    # type_of_interest = ECall #EMapGet
                    # if isinstance(e, type_of_interest):
                    #     print("got map get {} @ {}".format(pprint(e), cost))

                    if cost_model.is_monotonic() and best_cost is not None and cost > best_cost:
                        # if isinstance(e, type_of_interest):
                        #     print("too expensive: {}".format(pprint(e)))
                        continue
                    fp = fingerprint(e, g_examples, fvs, binders)
                    prev = seen.get(fp)
                    if prev is None:
                        seen[fp] = (cost, e, sz1)
                        cache.add(e, size=sz1)
                    else:
                        prev_cost, prev_exp, prev_size = prev
                        if cost < prev_cost:
                            # print("cost ceiling lowered for {}: {} --> {}".format(fp, prev_cost, cost))
                            cache.evict(prev_exp, prev_size)
                            cache.add(e, size=sz1)
                            seen[fp] = (cost, e, sz1)
                        else:
                            # if isinstance(e, type_of_interest):
                            #     print("dropping {}; already handled by {} @ {} (examples={})".format(pprint(e), pprint(prev_exp), prev_cost, repr(examples)))
                            continue

                    # # debug = "xxx" in name
                    # debug = name == "implicitFrom"
                    # if debug: print("got expr: {} : {} @ {}".format(pprint(e), pprint(e.type), sz1))

                    if e.type != type:
                        # if debug: print("    --> FAIL; I wanted {}".format(pprint(type)))
                        continue

                    # if debug: print("    --> OK!")

                    # print("{}| considering {} for {} [examples={}]".format(indent, pprint(e), name, g_examples))
                    # print("{}| considering {} @ {}".format(indent, pprint(e), sz1))
                    spec2 = subst(spec, { name : e })
                    # print("{}|{} ---> {}".format(indent, name, pprint(e)))
                    # print("{}|{}".format(indent, pprint(spec)))
                    # print("{}|{}".format(indent, pprint(spec2)))
                    # assert name not in (g.name for g in find_holes(spec2))
                    if not feasible(spec2, examples):
                        print("{}INFEASIBLE: {}".format(indent, pprint(spec2)))
                        continue
                    for d in find_consistent_exps(spec2, binders, examples, sz2, timeout=timeout):
                        cost = cost_model.cost(expand(e, d))
                        if best_cost is not None and cost > best_cost:
                            continue
                        if best_cost is None or cost < best_cost:
                            print("cost ceiling lowered for {}: {} --> {}".format(name, best_cost, cost))
                            best_cost = cost
                        # TODO: if monotonic, clean out cache
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

@typechecked
def synth(spec : Exp, binders : [EVar], vars : [EVar], timeout : Timeout):
    examples = []
    while True:
        for mapping in find_consistent_exps(spec, binders, examples, timeout=timeout):
            new_spec = expand(spec, mapping)

            print("considering: {}".format(pprint(new_spec)))
            if all(eval(new_spec, ex) for ex in examples):
                model = satisfy(EUnaryOp("not", new_spec).with_type(TBool()), vars=vars)
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
