from collections import defaultdict
import datetime
import itertools
import sys

from cozy.target_syntax import *
from cozy.typecheck import INT, BOOL
from cozy.syntax_tools import subst, replace, pprint, free_vars, BottomUpExplorer, BottomUpRewriter, equal, fresh_var, alpha_equivalent, all_exps
from cozy.common import Visitor, fresh_name, typechecked, unique, pick_to_sum, cross_product
from cozy.solver import satisfy, feasible
from cozy.evaluation import HoleException, eval, all_envs_for_hole
from cozy.timeouts import Timeout

def nested_dict(n, t):
    if n <= 0:
        return t()
    return defaultdict(lambda: nested_dict(n-1, t))

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
    def types(self):
        for d in self.data.values():
            yield from d.keys()
    def __iter__(self):
        for x in self.data.values():
            for y in x.values():
                for (size, es) in y.items():
                    for e in es:
                        yield (e, size)
    def __len__(self):
        return self.size
    def random_sample(self, n):
        import random
        es = [ e for (e, size) in self ]
        return random.sample(es, n)

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
    def visit_EEmptyList(self, e):
        return 0
    def visit_ESingleton(self, e):
        return 1
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
    def visit_EBinOp(self, e):
        cost = self.visit(e.e1) + self.visit(e.e2)
        if e.op == "in":
            cost += cardinality(e.e2)
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
    def visit(self, x):
        if isinstance(x, Exp) and not free_vars(x):
            return 0
        return super().visit(x)

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
            for a1 in cache.find(type=INT, size=sz1):
                for a2 in cache.find(type=INT, size=sz2):
                    yield EBinOp(a1, "+", a2).with_type(INT)
                    yield EBinOp(a1, "-", a2).with_type(INT)
                    yield EBinOp(a1, ">", a2).with_type(BOOL)
                    yield EBinOp(a1, "<", a2).with_type(BOOL)
                    yield EBinOp(a1, ">=", a2).with_type(BOOL)
                    yield EBinOp(a1, "<=", a2).with_type(BOOL)
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

class Learner(object):
    def __init__(self, target, binders, examples, cost_model, builder, timeout):
        self.binders = binders
        self.timeout = timeout
        self.cost_model = cost_model
        self.builder = builder
        self.seen = { } # fingerprint:(cost, e, size) map
        self.reset(examples, update_watched_exps=False)
        self.watch(target)

    def reset(self, examples, update_watched_exps=True):
        self.cache = Cache()
        self.current_size = 0
        self.examples = examples
        self.seen.clear()
        self.builder_iter = ()
        if update_watched_exps:
            self.update_watched_exps()

    def watch(self, new_target):
        self.target = new_target
        self.vars = free_vars(new_target)
        self.cost_ceiling = self.cost_model.cost(new_target)
        self.update_watched_exps()
        if self.cost_model.is_monotonic():
            seen = list(self.seen.items())
            for (fp, (cost, e, size)) in seen:
                if cost > self.cost_ceiling:
                    self.cache.evict(e, size)
                    del self.seen[fp]

    def update_watched_exps(self):
        # self.watched_exps = {
        #     self._fingerprint(e) : (e, self.cost_model.cost(e))
        #     for e in all_exps(self.target)
        #     if not isinstance(e, ELambda) }
        e = self.target
        self.watched_exps = {
            self._fingerprint(e) : (e, self.cost_model.cost(e)) }

    def _fingerprint(self, e):
        return fingerprint(e, self.examples, self.vars, self.binders)

    def next(self):
        while True:
            for e in self.builder_iter:

                if self.timeout is not None:
                    self.timeout.check()

                cost = self.cost_model.cost(e)

                if self.cost_model.is_monotonic() and cost > self.cost_ceiling:
                    continue

                fp = self._fingerprint(e)
                prev = self.seen.get(fp)

                if prev is None:
                    self.seen[fp] = (cost, e, self.current_size)
                    self.cache.add(e, size=self.current_size)
                else:
                    prev_cost, prev_exp, prev_size = prev
                    if cost < prev_cost:
                        # print("cost ceiling lowered for {}: {} --> {}".format(fp, prev_cost, cost))
                        self.cache.evict(prev_exp, prev_size)
                        self.cache.add(e, size=self.current_size)
                        self.seen[fp] = (cost, e, self.current_size)
                    else:
                        continue

                watched = self.watched_exps.get(fp)
                if watched is not None:
                    watched_e, watched_cost = watched
                    if cost < watched_cost:
                        return (watched_e, e)

            self.current_size += 1
            self.builder_iter = self.builder.build(self.cache, self.current_size)
            print("minor iteration {}, |cache|={}".format(self.current_size, len(self.cache)))

@typechecked
def improve(
        target : Exp,
        assumptions : [Exp],
        binders : [EVar],
        vars : [EVar],
        cost_model : CostModel,
        builder : Builder,
        timeout : Timeout):

    examples = []
    learner = Learner(target, binders, examples, cost_model, builder, timeout)
    while True:
        # 1. find any potential improvement to any sub-exp of target
        old_e, new_e = learner.next()

        # 2. substitute the improvement in (assert cost is lower)
        new_target = replace(target, old_e, new_e)
        assert cost_model.cost(new_target) < cost_model.cost(target)

        # 3. check
        formula = EAll(assumptions + [ENot(equal(target, new_target))])
        counterexample = satisfy(formula, vars=vars)
        if counterexample is not None:
            # a. if incorrect: add example, reset the learner
            examples.append(counterexample)
            print("new example: {}".format(counterexample))
            print("restarting with {} examples".format(len(examples)))
            learner.reset(examples)
        else:
            # b. if correct: yield it, watch the new target, goto 2
            print("found improvement: {} -----> {}".format(pprint(old_e), pprint(new_e)))
            print("cost: {} -----> {}".format(cost_model.cost(old_e), cost_model.cost(new_e)))
            learner.watch(new_target)
            target = new_target
            yield new_target
