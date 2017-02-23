from collections import defaultdict
import itertools
import sys

from cozy.target_syntax import *
from cozy.typecheck import INT, BOOL, is_numeric
from cozy.syntax_tools import subst, pprint, free_vars, BottomUpExplorer, BottomUpRewriter, equal, fresh_var, alpha_equivalent, all_exps, implies, mk_lambda, enumerate_fragments
from cozy.common import OrderedSet, ADT, Visitor, fresh_name, typechecked, unique, pick_to_sum, cross_product, OrderedDefaultDict, OrderedSet, nested_dict, group_by, find_one
from cozy.solver import satisfy, satisfiable, valid
from cozy.evaluation import eval, mkval
from cozy.cost_model import CostModel
from cozy.opts import Option

save_testcases = Option("save-testcases", str, "", metavar="PATH")
hyperaggressive_eviction = Option("hyperaggressive-eviction", bool, True)
reject_symmetric_binops = Option("reject-symmetric-binops", bool, True)
eliminate_vars = Option("eliminate-vars", bool, False)
reset_on_success = Option("reset-on-success", bool, False)

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
        try:
            self.data[self.tag(e.type)][e.type][size].remove(e)
            self.size -= 1
        except ValueError:
            # this happens if e is not in the list, which is fine
            pass
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

class ExpBuilder(object):
    def build(self, cache, size):
        raise NotImplementedError()

def _instantiate_examples(examples, binder, possible_values):
    for e in examples:
        found = 0
        if binder.id in e:
            yield e
            continue
            found += 1
        for possible_value in possible_values:
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

def instantiate_examples(watched_targets, examples, binders : [EVar]):
    # collect all the values that flow into the binders
    vals_by_type = defaultdict(OrderedSet)
    for e in watched_targets:
        for ex in examples:
            eval(e, ex, bind_callback=lambda arg, val: vals_by_type[arg.type].add(val))
    # instantiate examples with each possible combination of values
    for v in binders:
        examples = list(_instantiate_examples(examples, v, vals_by_type.get(v.type, ())))
    # print("Got {} instantiated examples".format(len(examples)), file=sys.stderr)
    # for ex in examples:
    #     print(" ---> " + repr(ex), file=sys.stderr)
    return examples

def fingerprint(e, examples):
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

class NoMoreImprovements(Exception):
    pass

oracle = None
def _on_exp(e, fate, *args):
    return
    # if (isinstance(e, EMapGet) or
    #         isinstance(e, EFilter) or
    #         (isinstance(e, EBinOp) and e.op == "==" and (isinstance(e.e1, EVar) or isinstance(e.e2, EVar))) or
    #         (isinstance(e, EBinOp) and e.op == ">=" and (isinstance(e.e1, EVar) or isinstance(e.e2, EVar)))):
    # if isinstance(e, EBinOp) and e.op == "+" and isinstance(e.type, TBag):
    # if hasattr(e, "_tag") and e._tag:
    # if isinstance(e, EFilter):
    # if fate in ("better", "new"):
    # if isinstance(e, EEmptyList):
    # if "commutative" in fate:
    # if any(alpha_equivalent(e, ee) for ee in all_exps(_TARGET)):
    # if isinstance(e, EBinOp) and e.op == "-" and isinstance(e.e1, EUnaryOp) and e.e1.op == "sum" and isinstance(e.e2, EUnaryOp) and e.e2.op == "sum":
    # if oracle is not None and any(alpha_equivalent(e, x) for x in all_exps(oracle)):
    # if oracle is not None and any(e.type == x.type and valid(equal(e, x)) for x in all_exps(oracle) if not isinstance(x, ELambda)):
    if hasattr(e, "_tag"):
        print(" ---> [{}, {}] {}; {}".format(fate, pprint(e.type), pprint(e), ", ".join((pprint(e) if isinstance(e, ADT) else str(e)) for e in args)), file=sys.stderr)

class Learner(object):
    def __init__(self, target, assumptions, binders, legal_free_vars, examples, cost_model, builder, stop_callback):
        self.binders = OrderedSet(binders)
        self.legal_free_vars = legal_free_vars
        self.stop_callback = stop_callback
        self.cost_model = cost_model
        self.builder = builder
        self.seen = { } # map of {fingerprint:(cost, [(e, size)])}
        self.reset(examples, update_watched_exps=False)
        self.watch(target, assumptions)

    def reset(self, examples, update_watched_exps=True):
        self.cache = Cache()
        self.current_size = 0
        self.examples = examples
        self.seen.clear()
        self.builder_iter = ()
        self.last_progress = 0
        if update_watched_exps:
            self.update_watched_exps()

    def watch(self, new_target, assumptions):
        self.target = new_target
        new_roots = []
        for e in itertools.chain(all_exps(new_target), all_exps(assumptions)):
            if e in new_roots:
                continue
            if not isinstance(e, ELambda) and all(v in self.legal_free_vars for v in free_vars(e)):
                self._fingerprint(e)
                new_roots.append(e)
        self.roots = new_roots
        self.update_watched_exps()
        if self.cost_model.is_monotonic():
            seen = list(self.seen.items())
            n = 0
            for (fp, (cost, exps)) in seen:
                if cost > self.cost_ceiling:
                    for (e, size) in exps:
                        _on_exp(e, "evicted due to lowered cost ceiling [cost={}, ceiling={}]".format(cost, self.cost_ceiling))
                        self.cache.evict(e, size)
                        n += 1
                    del self.seen[fp]
            if n:
                print("evicted {} elements".format(n))

    def update_watched_exps(self):
        self.cost_ceiling = self.cost_model.cost(self.target)
        self.watched_exps = []
        for (a, e, r) in enumerate_fragments(self.target):
            if isinstance(e, ELambda) or any(v not in self.legal_free_vars for v in free_vars(e)):
                continue
            cost = self.cost_model.cost(e)
            self.watched_exps.append((e, r, cost, EAll(a)))

    def _examples_for(self, e):
        binders = [b for b in free_vars(e) if b in self.binders]
        return instantiate_examples((self.target,), self.examples, binders)

    def _fingerprint(self, e, examples=None):
        return fingerprint(e, self._examples_for(e))

    def next(self):
        while True:
            for e in self.builder_iter:
                if self.stop_callback():
                    raise StopException()

                cost = self.cost_model.cost(e)

                if self.cost_model.is_monotonic() and cost > self.cost_ceiling:
                    _on_exp(e, "too expensive", cost, self.cost_ceiling)
                    continue

                fp = self._fingerprint(e)
                prev = self.seen.get(fp)

                if prev is None:
                    self.seen[fp] = (cost, [(e, self.current_size)])
                    self.cache.add(e, size=self.current_size)
                    self.last_progress = self.current_size
                    _on_exp(e, "new")
                else:
                    prev_cost, prev_exps = prev
                    if e in (ee for (ee, size) in prev_exps):
                        _on_exp(e, "duplicate")
                        continue
                    elif cost == prev_cost:
                        self.cache.add(e, size=self.current_size)
                        self.seen[fp][1].append((e, self.current_size))
                        self.last_progress = self.current_size
                        _on_exp(e, "equivalent", *[e for (e, cost) in prev_exps])
                    elif cost < prev_cost:
                        for (prev_exp, prev_size) in prev_exps:
                            self.cache.evict(prev_exp, prev_size)
                            if self.cost_model.is_monotonic() and hyperaggressive_eviction.value:
                                for (cached_e, size) in list(self.cache):
                                    if prev_exp in all_exps(cached_e):
                                        _on_exp(cached_e, "evicted since it contains", prev_exp)
                                        self.cache.evict(cached_e, size)
                        self.cache.add(e, size=self.current_size)
                        self.seen[fp] = (cost, [(e, self.current_size)])
                        self.last_progress = self.current_size
                        _on_exp(e, "better", *[e for (e, cost) in prev_exps])
                    else:
                        _on_exp(e, "worse", *[e for (e, cost) in prev_exps])
                        continue

                for (watched_e, r, watched_cost, assumptions) in self.watched_exps:
                    if watched_e.type != e.type or watched_cost < cost:
                        continue
                    if e == watched_e:
                        continue
                    eqfp = self._fingerprint(implies(assumptions, EEq(e, watched_e)))
                    if all(eqfp[i] for i in range(1, len(eqfp))):
                        return (watched_e, e, r)

            if self.last_progress < (self.current_size+1) // 2:
                raise NoMoreImprovements("hit termination condition")

            self.current_size += 1
            self.builder_iter = self.builder.build(self.cache, self.current_size)
            if self.current_size == 1:
                self.builder_iter = itertools.chain(self.builder_iter, iter(self.roots))
            print("minor iteration {}, |cache|={}".format(self.current_size, len(self.cache)))

@typechecked
def fixup_binders(e : Exp, binders_to_use : [EVar], allow_add=False) -> Exp:
    binders_by_type = group_by(binders_to_use, lambda b: b.type)
    class V(BottomUpRewriter):
        def visit_ELambda(self, e):
            if e.arg in binders_by_type[e.arg.type]:
                return ELambda(e.arg, self.visit(e.body))
            fvs = free_vars(e.body)
            legal_repls = [ b for b in binders_by_type[e.arg.type] if b not in fvs ]
            if not legal_repls:
                if allow_add:
                    print("Adding aux binder {} and returning {}".format(e.arg, pprint(ELambda(e.arg, e.body))), file=sys.stderr)
                    binders_to_use.append(e.arg)
                    binders_by_type[e.arg.type].append(e.arg)
                    return ELambda(e.arg, self.visit(e.body))
                else:
                    raise Exception("No legal binder to use for {}".format(e))
            b = legal_repls[0]
            return ELambda(b, self.visit(subst(e.body, { e.arg.id : b })))
    return V().visit(e)

COMMUTATIVE_OPERATORS = set(("==", "and", "or", "+"))

class FixedBuilder(ExpBuilder):
    def __init__(self, wrapped_builder, binders_to_use, assumptions : Exp):
        self.wrapped_builder = wrapped_builder
        self.binders_to_use = binders_to_use
        self.assumptions = assumptions
    def build(self, cache, size):
        for e in self.wrapped_builder.build(cache, size):
            try:
                orig = e
                # print(hasattr(orig, "_tag"), file=sys.stderr)
                e = fixup_binders(e, self.binders_to_use)
                if hasattr(orig, "_tag"):
                    e._tag = orig._tag
            except Exception:
                _on_exp(e, "unable to rename binders")
                continue
                print("WARNING: skipping built expression {}".format(pprint(e)), file=sys.stderr)

            if reject_symmetric_binops.value and size > 1 and isinstance(e, EBinOp) and e.op in COMMUTATIVE_OPERATORS and e.e2 < e.e1:
                _on_exp(e, "rejecting symmetric use of commutative operator")
                continue

            # all sets must have distinct values
            if isinstance(e.type, TSet):
                if not valid(implies(self.assumptions, EUnaryOp("unique", e).with_type(BOOL))):
                    raise Exception("insanity: values of {} are not distinct".format(e))

            # experimental criterion: "the" must be a 0- or 1-sized collection
            if isinstance(e, EUnaryOp) and e.op == "the":
                len = EUnaryOp("sum", EMap(e.e, mk_lambda(e.type, lambda x: ENum(1).with_type(INT))).with_type(TBag(INT))).with_type(INT)
                if not valid(implies(self.assumptions, EBinOp(len, "<=", ENum(1).with_type(INT)).with_type(BOOL))):
                    _on_exp(e, "rejecting illegal application of 'the': could have >1 elems")
                    continue
                if not satisfiable(EAll([self.assumptions, equal(len, ENum(0).with_type(INT))])):
                    _on_exp(e, "rejecting illegal application of 'the': cannot be empty")
                    continue
                if not satisfiable(EAll([self.assumptions, equal(len, ENum(1).with_type(INT))])):
                    _on_exp(e, "rejecting illegal application of 'the': always empty")
                    continue

            # filters must *do* something
            # This prevents degenerate cases where the synthesizer uses filter
            # expressions to artificially lower the estimated cardinality of a
            # collection.
            if isinstance(e, EFilter):
                if not satisfiable(EAll([self.assumptions, ENot(equal(e, e.e))])):
                    _on_exp(e, "rejecting no-op filter")
                    continue

            # # map gets must be provably in the map
            # if isinstance(e, EMapGet):
            #     if not valid(implies(self.assumptions, EBinOp(e.key, BOp.In, EMapKeys(e.map).with_type(TBag(e.map.type.k))).with_type(BOOL))):
            #         _on_exp(e, "rejecting potential map lookup miss")
            #         continue

            # # constructed maps cannot always be empty
            # if isinstance(e, EMakeMap):
            #     if not satisfiable(EAll([self.assumptions, EUnaryOp(UOp.Exists, e.e).with_type(BOOL)])):
            #         _on_exp(e, "rejecting empty map")
            #         continue

            yield e

class VarElimBuilder(ExpBuilder):
    def __init__(self, wrapped_builder, illegal_vars : [EVar]):
        self.wrapped_builder = wrapped_builder
        self.illegal_vars = set(illegal_vars)
    def build(self, cache, size):
        for e in self.wrapped_builder.build(cache, size):
            if not any(v in self.illegal_vars for v in free_vars(e)):
                yield e
            else:
                _on_exp(e, "contains illegal vars")

def truncate(s):
    if len(s) > 60:
        return s[:60] + "..."
    return s

def can_elim_var(spec : Exp, assumptions : Exp, v : EVar):
    vv = fresh_var(v.type)
    return valid(implies(EAll([assumptions, subst(assumptions, {v.id:vv})]), equal(spec, subst(spec, {v.id:vv}))))

@typechecked
def construct_value(t : Type) -> Exp:
    if is_numeric(t):
        e = ENum(0)
    elif t == BOOL:
        e = F
    elif t == STRING:
        e = EStr("")
    elif isinstance(t, TBag):
        e = EEmptyList()
    elif isinstance(t, TTuple):
        e = ETuple(tuple(construct_value(tt) for tt in t.ts))
    elif isinstance(t, TRecord):
        e = EMakeRecord(tuple((f, construct_value(tt)) for (f, tt) in t.fields))
    elif isinstance(t, TEnum):
        e = EEnumEntry(t.cases[0])
    elif isinstance(t, THandle):
        e = EHandle(construct_value(INT), construct_value(t.value_type))
    else:
        raise NotImplementedError(pprint(t))
    e = e.with_type(t)
    assert eval(e, {}) == mkval(t)
    return e

@typechecked
def improve(
        target : Exp,
        assumptions : Exp,
        binders : [EVar],
        cost_model : CostModel,
        builder : ExpBuilder,
        stop_callback,
        hints : [Exp] = [],
        examples = None):

    binders = list(binders)
    target = fixup_binders(target, binders, allow_add=False)
    assumptions = fixup_binders(assumptions, binders, allow_add=False)
    builder = FixedBuilder(builder, binders, assumptions)

    vars = list(free_vars(target) | free_vars(assumptions))
    if eliminate_vars.value:
        illegal_vars = [v for v in vars if can_elim_var(target, assumptions, v)]
        builder = VarElimBuilder(builder, illegal_vars)

    if examples is None:
        examples = []
    learner = Learner(target, assumptions, binders, vars + binders, examples, cost_model, builder, stop_callback)
    try:
        while True:
            # 1. find any potential improvement to any sub-exp of target
            try:
                old_e, new_e, repl = learner.next()
            except NoMoreImprovements:
                break

            # 2. substitute-in the improvement
            new_target = repl(new_e)

            bad_var = find_one(free_vars(new_target), lambda v: v not in vars)
            if bad_var is not None:
                print("oops")

            # 3. check
            print("Found candidate replacement [{}] for [{}]".format(pprint(new_e), pprint(old_e)))
            formula = EAll([assumptions, ENot(equal(target, new_target))])
            counterexample = satisfy(formula, vars=vars)
            if counterexample is not None:
                if counterexample in examples:
                    print("duplicate example: {}".format(repr(counterexample)))
                    print("old target = {}".format(pprint(target)))
                    print("new target = {}".format(pprint(new_target)))
                    print("old fp = {}".format(learner._fingerprint(old_e)))
                    print("new fp = {}".format(learner._fingerprint(new_e)))
                    print("old target fp = {}".format(learner._fingerprint(target)))
                    print("new target fp = {}".format(learner._fingerprint(new_target)))
                    raise Exception("got a duplicate example")
                # a. if incorrect: add example, reset the learner
                examples.append(counterexample)
                print("new example: {}".format(truncate(repr(counterexample))))
                print("restarting with {} examples".format(len(examples)))
                learner.reset(examples)
            else:
                # b. if correct: yield it, watch the new target, goto 1

                while bad_var:
                    print("Eliminating bad free var {}".format(pprint(bad_var)))
                    new_value = construct_value(bad_var.type)
                    subst_repl = { bad_var.id: new_value }
                    new_target = subst(new_target, subst_repl)
                    new_e = subst(new_e, subst_repl)
                    bad_var = find_one(free_vars(new_target), lambda v: v not in vars)

                old_cost = cost_model.cost(target)
                new_cost = cost_model.cost(new_target)
                if new_cost > old_cost:
                    print("WHOOPS! COST GOT WORSE!")
                    if save_testcases.value:
                        with open(save_testcases.value, "a") as f:
                            f.write("def testcase():\n")
                            f.write("    costmodel = {}\n".format(repr(cost_model)))
                            f.write("    old_e = {}\n".format(repr(old_e)))
                            f.write("    new_e = {}\n".format(repr(new_e)))
                            f.write("    target = {}\n".format(repr(target)))
                            f.write("    new_target = {}\n".format(repr(new_target)))
                            f.write("    if costmodel.cost(new_e) <= costmodel.cost(old_e) and costmodel.cost(new_target) > costmodel.cost(target):\n")
                            f.write("        for x in [old_e, new_e, target, new_target]:\n")
                            f.write("            pprint_reps(infer_rep(costmodel.state_vars, x))\n")
                            f.write('            print("cost = {}".format(costmodel.cost(x)))\n')
                            f.write("        assert False\n")
                    continue
                if new_cost == old_cost:
                    continue
                print("found improvement: {} -----> {}".format(pprint(old_e), pprint(new_e)))
                print("cost: {} -----> {}".format(old_cost, new_cost))
                if reset_on_success.value:
                    learner.reset(examples, update_watched_exps=False)
                learner.watch(new_target, assumptions)
                target = new_target
                yield new_target
    except KeyboardInterrupt:
        for e in learner.cache.random_sample(50):
            print(pprint(e))
        raise
