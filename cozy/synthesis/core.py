from collections import OrderedDict
import datetime
import itertools
import sys

from cozy.target_syntax import *
from cozy.typecheck import INT, BOOL
from cozy.syntax_tools import subst, replace, pprint, free_vars, BottomUpExplorer, BottomUpRewriter, equal, fresh_var, alpha_equivalent, all_exps, implies, mk_lambda
from cozy.common import Visitor, fresh_name, typechecked, unique, pick_to_sum, cross_product
from cozy.solver import satisfy, valid
from cozy.evaluation import HoleException, eval, all_envs_for_hole, mkval

MISSING = object()
class OrderedDefaultDict(OrderedDict):
    def __init__(self, factory):
        super().__init__()
        self.factory = factory
    def __missing__(self, k):
        v = self.get(k, MISSING)
        if v is MISSING:
            v = self.factory()
            self[k] = v
        return v

def nested_dict(n, t):
    if n <= 0:
        return t()
    return OrderedDefaultDict(lambda: nested_dict(n-1, t))

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
        return random.sample(es, min(n, len(es)))

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
    def visit_EGetField(self, e):
        return 1000
    def visit_ETupleGet(self, e):
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
            raise NotImplementedError(e)
    def visit_EUnaryOp(self, e):
        if e.op == "the":
            return 1000 # TODO???
        else:
            raise NotImplementedError(e)
    def visit_EMap(self, e):
        return self.visit(e.e)
    def visit_EFlatMap(self, e):
        return self.visit(e.e) * self.visit(e.f.body)
    def visit_Exp(self, e):
        raise NotImplementedError(e)

cardinality = CardinalityVisitor().visit

class MemoryUsageCostModel(CostModel, BottomUpExplorer):
    def best_case_cost(self, e):
        try:
            return self.visit(e) + e.size() / 100
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
        if e.op == "+" and isinstance(e.e1.type, TBag):
            return cardinality(e.e1) + cardinality(e.e2)
        return 1 # TODO: sizeof(e.type)
    def visit_ESingleton(self, e):
        return self.visit(e.e)
    def visit_EEmptyList(self, e):
        return 0
    def visit_EMap(self, e):
        return cardinality(e.e) * self.visit(e.f.body)
    def visit_EFlatMap(self, e):
        return cardinality(e.e) * self.visit(e.f.body)
    def visit_EFilter(self, e):
        return cardinality(e) # TODO: c * sizeof(e.type.t)
    def visit_EMakeMap(self, e):
        return self.visit(e.value.body)
    def visit_EMapGet(self, e):
        assert isinstance(e.map, EMakeMap)
        return self.visit(e.map.value.apply_to(EFilter(e.map.e, ELambda(e.map.key.arg, equal(e.map.key.arg, fresh_var(e.map.key.arg.type))))))
    def visit_EAlterMaybe(self, e):
        return self.visit(e.f.body)
    def visit_EGetField(self, e):
        return 1 # TODO: sizeof(e.type)
    def visit_ENum(self, e):
        return 1 # TODO: sizeof(int)
    def visit_EEnumEntry(self, e):
        return 1 # TODO: sizeof(enum)
    def visit_ECall(self, e):
        return 1 # TODO: sizeof(e.type), or cardinality estimation
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
        return cost + 0.01
    def visit_EBinOp(self, e):
        cost = self.visit(e.e1) + self.visit(e.e2)
        if e.op == "==" and isinstance(e.e1.type, TBag):
            cost += cardinality(e.e1) + cardinality(e.e2)
        return cost + 0.01
    def visit_EMap(self, e):
        return self.visit(e.e) + cardinality(e.e) * self.visit(e.f.body)
    def visit_EFlatMap(self, e):
        return self.visit(EFlatten(EMap(e.e, e.f)))
    def visit_EFilter(self, e):
        return self.visit(e.e) + cardinality(e.e) * self.visit(e.p.body)
    def visit_EMakeMap(self, e):
        return self.visit(e.e) + cardinality(e.e) * (self.visit(e.key.body) + self.visit(e.value.body))
    def join(self, x, child_costs):
        if not isinstance(x, Exp):
            return 0
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
            for e in itertools.chain(cache.find(type=TBag(INT), size=size-1), cache.find(type=TSet(INT), size=size-1)):
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
                    # yield EBinOp(a1, "+", a2).with_type(INT)
                    # yield EBinOp(a1, "-", a2).with_type(INT)
                    yield EBinOp(a1, ">", a2).with_type(BOOL)
                    yield EBinOp(a1, "<", a2).with_type(BOOL)
                    yield EBinOp(a1, ">=", a2).with_type(BOOL)
                    yield EBinOp(a1, "<=", a2).with_type(BOOL)
            for a1 in cache.find(type=TBag, size=sz1):
                if not isinstance(a1.type.t, THandle):
                    continue
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
    elif isinstance(value_type, TSet) or isinstance(value_type, TBag):
        for x in value:
            yield from values_of_type(x, value_type.t, desired_type)
    else:
        # I think this is OK since all values for bound vars are pulled from
        # bags or other collections.
        pass

def instantiate_examples(examples, vars, binder):
    for e in examples:
        found = 0
        if binder.id in e:
            yield e
            found += 1
        for v in vars:
            for possible_value in unique(values_of_type(e[v.id], v.type, binder.type)):
                # print("possible value for {}: {}".format(pprint(binder.type), repr(possible_value)))
                e2 = dict(e)
                e2[binder.id] = possible_value
                yield e2
                found += 1
            # print("got {} ways to instantiate {}".format(found, binder.id))
            if not found:
                e2 = dict(e)
                e2[binder.id] = mkval(binder.type)
                yield e2

def fingerprint(e, examples, vars : {EVar}, binders : [EVar]):
    fvs = free_vars(e)
    for v in binders:
        examples = list(instantiate_examples(examples, vars, v))
    return (e.type,) + tuple(eval(e, ex) for ex in examples)

def make_constant_of_type(t):
    class V(Visitor):
        def visit_TInt(self, t):
            return ENum(0).with_type(t)
        def visit_TBool(self, t):
            return EBool(False).with_type(t)
        def visit_TBag(self, t):
            return EEmptyList().with_type(t)
        def visit_Type(self, t):
            raise NotImplementedError(t)
    return V().visit(t)

class StopException(Exception):
    pass

class Learner(object):
    def __init__(self, target, binders, examples, cost_model, builder, stop_callback):
        self.binders = binders
        self.stop_callback = stop_callback
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
        self.last_progress = 0
        if update_watched_exps:
            self.update_watched_exps()

    def watch(self, new_target):
        self.target = new_target
        self.vars = free_vars(new_target)
        self.cost_ceiling = self.cost_model.cost(new_target)
        self.update_watched_exps()
        if self.cost_model.is_monotonic():
            seen = list(self.seen.items())
            n = 0
            for (fp, (cost, e, size)) in seen:
                if cost > self.cost_ceiling:
                    self.cache.evict(e, size)
                    del self.seen[fp]
                    n += 1
            if n:
                print("evicted {} elements".format(n))

    def update_watched_exps(self):
        e = self.target
        self.watched_exps = {}
        for e in all_exps(self.target):
            if isinstance(e, ELambda):
                continue
            try:
                self.watched_exps[self._fingerprint(e)] = (e, self.cost_model.cost(e))
            except Exception:
                print("WARNING: unable to watch expression {}".format(pprint(e)))
                continue

    def _fingerprint(self, e):
        return fingerprint(e, self.examples, self.vars, self.binders)

    def _on_exp(self, e, fate, *args):
        return
        if isinstance(e, EMapGet):
            print(" ---> [{}] {} {}".format(fate, pprint(e), ", ".join(pprint(e) for e in args)))
        if isinstance(e, EBinOp) and e.op == "==":
            print(" ---> [{}] {} {}".format(fate, pprint(e), ", ".join(pprint(e) for e in args)))

    def forget_most_recent(self):
        (e, size, fp) = self.most_recent
        self.cache.evict(e, size)
        self.seen[fp] = self.overwritten
        self.most_recent = self.overwritten = None

    def next(self):
        while True:
            for e in self.builder_iter:

                if self.stop_callback():
                    raise StopException()

                cost = self.cost_model.cost(e)

                if self.cost_model.is_monotonic() and cost > self.cost_ceiling:
                    self._on_exp(e, "too expensive")
                    continue

                fp = self._fingerprint(e)
                prev = self.seen.get(fp)

                if prev is None:
                    self.overwritten = None
                    self.most_recent = (e, self.current_size, fp)
                    self.seen[fp] = (cost, e, self.current_size)
                    self.cache.add(e, size=self.current_size)
                    self.last_progress = self.current_size
                    self._on_exp(e, "new")
                else:
                    prev_cost, prev_exp, prev_size = prev
                    if cost < prev_cost:
                        self.overwritten = prev
                        self.most_recent = (e, self.current_size, fp)
                        # print("cost ceiling lowered for {}: {} --> {}".format(fp, prev_cost, cost))
                        self.cache.evict(prev_exp, prev_size)
                        self.cache.add(e, size=self.current_size)
                        self.seen[fp] = (cost, e, self.current_size)
                        self.last_progress = self.current_size
                        self._on_exp(e, "better")
                    else:
                        self._on_exp(e, "worse", prev_exp)
                        continue

                watched = self.watched_exps.get(fp)
                if watched is not None:
                    watched_e, watched_cost = watched
                    if cost < watched_cost:
                        print("Found potential improvement [{}] for [{}]".format(pprint(e), pprint(watched_e)))
                        # while set(self.binders) & free_vars(e):
                        #     print("stripping binders from {}".format(e))
                        #     b = list(set(self.binders) & free_vars(e))[0]
                        #     e = subst(e, { b.id : make_constant_of_type(b.type) })
                        return (watched_e, e)

            if self.last_progress < (self.current_size+1) // 2:
                raise StopException("hit termination condition")

            self.current_size += 1
            self.builder_iter = self.builder.build(self.cache, self.current_size)
            print("minor iteration {}, |cache|={}".format(self.current_size, len(self.cache)))

@typechecked
def fixup_binders(e : Exp, binders_to_use : [EVar]) -> Exp:
    class V(BottomUpRewriter):
        def visit_ELambda(self, e):
            body = self.visit(e.body)
            if e.arg in binders_to_use:
                return ELambda(e.arg, body)
            if not any(b.type == e.arg.type for b in binders_to_use):
                # print("WARNING: I am assuming that subexpressions of [{}] never appear in isolation".format(pprint(e)))
                return ELambda(e.arg, body)
            fvs = free_vars(body)
            legal_repls = [ b for b in binders_to_use if b not in fvs and b.type == e.arg.type ]
            if not legal_repls:
                raise Exception("No legal binder to use for {}".format(e))
            b = legal_repls[0]
            return ELambda(b, subst(body, { e.arg.id : b }))
    return V().visit(e)

class FixedBuilder(ExpBuilder):
    def __init__(self, wrapped_builder, binders_to_use, assumptions : Exp):
        self.wrapped_builder = wrapped_builder
        self.binders_to_use = binders_to_use
        self.assumptions = assumptions
    def build(self, cache, size):
        for e in self.wrapped_builder.build(cache, size):
            try:
                e = fixup_binders(e, self.binders_to_use)
            except Exception:
                continue
                import sys
                print("WARNING: skipping built expression {}".format(pprint(e)), file=sys.stderr)

            # experimental criterion: bags of handles must have distinct values
            if isinstance(e.type, TBag) and isinstance(e.type.t, THandle):
                if not valid(implies(self.assumptions, EUnaryOp("unique", e).with_type(BOOL))):
                    # print("rejecting non-unique {}".format(pprint(e)))
                    continue

            # all sets must have distinct values
            if isinstance(e.type, TSet):
                if not valid(implies(self.assumptions, EUnaryOp("unique", e).with_type(BOOL))):
                    raise Exception("insanity: values of {} are not distinct".format(e))

            # experimental criterion: "the" must be a 0- or 1-sized collection
            if isinstance(e, EUnaryOp) and e.op == "the":
                len = EUnaryOp("sum", EMap(e.e, mk_lambda(e.type, lambda x: ENum(1).with_type(INT))).with_type(TBag(INT))).with_type(INT)
                if not valid(implies(self.assumptions, EBinOp(len, "<=", ENum(1).with_type(INT)))):
                    # print("rejecting illegal application of 'the': {}".format(pprint(e)))
                    continue
                if not satisfy(EAll([self.assumptions, equal(len, ENum(0).with_type(INT))])):
                    # print("rejecting illegal application of 'the': {}".format(pprint(e)))
                    continue
                if not satisfy(EAll([self.assumptions, equal(len, ENum(1).with_type(INT))])):
                    # print("rejecting illegal application of 'the': {}".format(pprint(e)))
                    continue

            # filters must *do* something
            # This prevents degenerate cases where the synthesizer uses filter
            # expressions to artificially lower the estimated cardinality of a
            # collection.
            if isinstance(e, EFilter):
                if not valid(implies(self.assumptions, ENot(equal(e, e.e)))):
                    continue

            yield e

@typechecked
def improve(
        target : Exp,
        assumptions : Exp,
        binders : [EVar],
        cost_model : CostModel,
        builder : Builder,
        stop_callback):

    target = fixup_binders(target, binders)
    builder = FixedBuilder(builder, binders, assumptions)

    vars = list(free_vars(target))
    examples = []
    learner = Learner(target, binders, examples, cost_model, builder, stop_callback)
    try:
        while True:
            # 1. find any potential improvement to any sub-exp of target
            old_e, new_e = learner.next()

            # 2. substitute the improvement in (assert cost is lower)
            new_target = replace(target, old_e, new_e)
            assert cost_model.cost(new_target) < cost_model.cost(target), "whoops: {} ----> {}".format(target, new_target)

            if (free_vars(new_target) - set(vars)):
                print("oops, candidate {} has weird free vars".format(pprint(new_target)))
                learner.forget_most_recent()
                continue

            # 3. check
            formula = EAll([assumptions, ENot(equal(target, new_target))])
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
    except KeyboardInterrupt:
        for e in learner.cache.random_sample(50):
            print(pprint(e))
        raise
