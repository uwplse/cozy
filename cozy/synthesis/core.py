from collections import defaultdict, OrderedDict
import itertools
import sys

from cozy.target_syntax import *
from cozy.typecheck import INT, BOOL
from cozy.syntax_tools import subst, pprint, free_vars, BottomUpExplorer, BottomUpRewriter, equal, fresh_var, alpha_equivalent, all_exps, implies, mk_lambda, enumerate_fragments
from cozy.common import OrderedSet, ADT, Visitor, fresh_name, typechecked, unique, pick_to_sum, cross_product, OrderedDefaultDict, OrderedSet, group_by, find_one
from cozy.solver import satisfy, satisfiable, valid
from cozy.evaluation import eval, eval_bulk, mkval, construct_value, uneval
from cozy.cost_model import CostModel
from cozy.opts import Option
from cozy.pools import RUNTIME_POOL, STATE_POOL

from .cache import Cache

save_testcases = Option("save-testcases", str, "", metavar="PATH")
hyperaggressive_culling = Option("hyperaggressive-culling", bool, False)
hyperaggressive_eviction = Option("hyperaggressive-eviction", bool, True)
reject_symmetric_binops = Option("reject-symmetric-binops", bool, False)
eliminate_vars = Option("eliminate-vars", bool, False)
reset_on_success = Option("reset-on-success", bool, False)
enforce_seen_wf = Option("enforce-seen-set-well-formed", bool, False)
enforce_strong_progress = Option("enforce-strong-progress", bool, True)

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
    return (e.type,) + tuple(eval_bulk(e, examples))

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

class ContextMap(object):
    VALUE = "value"
    def __init__(self):
        self.m = { }
    def _lookup(self, ctx, create=False):
        k = sorted(ctx)
        m = self.m
        for v in k:
            m2 = m.get(v)
            if m2 is None:
                if create:
                    m2 = { }
                    m[v] = m2
                else:
                    raise KeyError(ctx)
            m = m2
        return m
    def __setitem__(self, ctx : {EVar}, value):
        self._lookup(ctx, create=True)[ContextMap.VALUE] = value
    def __getitem__(self, ctx : {EVar}):
        return self._lookup(ctx, create=False)[ContextMap.VALUE]
    def _print(self, m):
        for (k, v) in m.items():
            if k == ContextMap.VALUE:
                yield "-> {}".format(v)
            else:
                for s in self._print(v):
                    yield "{} {}".format(pprint(k), s)
    def __str__(self):
        return "\n".join(self._print(self.m))

class BehaviorIndex(object):
    VALUE = "value"
    def __init__(self):
        self.data = OrderedDict()
    def put(self, e, assumptions, examples, data):
        ok      = [True] + eval_bulk(assumptions, examples)
        results = [e.type] + eval_bulk(e, examples)
        m = self.data
        for b, r in zip(ok, results):
            k = any if not b else r
            m2 = m.get(k)
            if m2 is None:
                m2 = OrderedDict()
                m[k] = m2
            m = m2
        l = m.get(BehaviorIndex.VALUE)
        if l is None:
            l = []
            m[BehaviorIndex.VALUE] = l
        l.append(data)
    def search(self, behavior):
        q = [(0, self.data)]
        while q:
            (i, m) = q.pop()
            if m is None:
                continue
            if i >= len(behavior):
                yield from m.get(BehaviorIndex.VALUE, [])
            else:
                q.append((i+1, m.get(any)))
                q.append((i+1, m.get(behavior[i])))
    def _pr(self, m):
        if BehaviorIndex.VALUE in m:
            yield str(m[BehaviorIndex.VALUE])
            return
        for k, v in m.items():
            for s in self._pr(v):
                yield "{} > {}".format("*" if k is any else pprint(k) if isinstance(k, ADT) else repr(k), s)
    def __str__(self):
        s = "Behavior Index\n"
        for line in self._pr(self.data):
            s += "  " + line + "\n"
        return s

class Learner(object):
    def __init__(self, target, assumptions, binders, args, legal_free_vars, examples, cost_model, builder, stop_callback):
        self.binders = OrderedSet(binders)
        self.args = OrderedSet(args)
        self.legal_free_vars = legal_free_vars
        self.stop_callback = stop_callback
        self.cost_model = cost_model
        self.builder = builder
        self.seen = { } # map of { (pool, fingerprint) : (cost, [(e, size)]) }
        self.reset(examples, update_watched_exps=False)
        self.watch(target, assumptions)

    def reset(self, examples, update_watched_exps=True):
        self.cache = Cache(binders=self.binders, args=self.args)
        self.current_size = 0
        self.examples = examples
        self.seen.clear()
        self.builder_iter = ()
        self.last_progress = 0
        self.backlog = None
        self.backlog_counter = 0
        if update_watched_exps:
            self.update_watched_exps()

    def _check_seen_wf(self):
        if enforce_seen_wf.value:
            for ((pool, fp), (cost, exps)) in self.seen.items():
                for (e, size) in exps:
                    fpnow = self._fingerprint(e)
                    if fp != fpnow:
                        print("#" * 40)
                        print(pprint(e))
                        print(fp)
                        print(fpnow)
                        assert False

    def fix_seen(self):
        print("fixing seen set...")
        new_seen = { }
        for ((pool, fp), (cost, exps)) in self.seen.items():
            for item in exps:
                e, size = item
                fpnow = self._fingerprint(e)
                k = (pool, fpnow)
                val = new_seen.get(k)
                if val is not None:
                    val[1].append(item)
                else:
                    new_seen[k] = (cost, [item])
        self.seen = new_seen
        self._check_seen_wf()
        print("finished fixing seen set")

    def watch(self, new_target, assumptions):
        self._check_seen_wf()
        self.backlog_counter = 0
        self.target = new_target
        self.update_watched_exps()
        self.roots = []
        for (e, r, cost, a, pool, bound) in self.watched_exps:
            _on_exp(e, "new root")
            self.roots.append((e, pool))
        # new_roots = []
        # for e in itertools.chain(all_exps(new_target), all_exps(assumptions)):
        #     if e in new_roots:
        #         continue
        #     if not isinstance(e, ELambda) and all(v in self.legal_free_vars for v in free_vars(e)):
        #         self._fingerprint(e)
        #         new_roots.append(e)
        # self.roots = new_roots
        if self.cost_model.is_monotonic() or hyperaggressive_culling.value:
            seen = list(self.seen.items())
            n = 0
            for ((pool, fp), (cost, exps)) in seen:
                if cost > self.cost_ceiling:
                    for (e, size) in exps:
                        _on_exp(e, "evicted due to lowered cost ceiling [cost={}, ceiling={}]".format(cost, self.cost_ceiling))
                        self.cache.evict(e, size=size, pool=pool)
                        n += 1
                    del self.seen[(pool, fp)]
            if n:
                print("evicted {} elements".format(n))
        self._check_seen_wf()

    def update_watched_exps(self):
        self.cost_ceiling = self.cost_model.cost(self.target, RUNTIME_POOL)
        self.watched_exps = []
        sv_depth = 0
        def pre_visit(obj):
            nonlocal sv_depth
            if isinstance(obj, EStateVar):
                sv_depth += 1
            return True
        def post_visit(obj):
            nonlocal sv_depth
            if isinstance(obj, EStateVar):
                sv_depth -= 1
        self.all_examples = instantiate_examples((self.target,), self.examples, self.binders)
        self.behavior_index = BehaviorIndex()
        for (a, e, r, bound) in enumerate_fragments(self.target, pre_visit=pre_visit, post_visit=post_visit):
            if isinstance(e, ELambda) or any(v not in self.legal_free_vars for v in free_vars(e)):
                continue
            a = [aa for aa in a if all(v in self.legal_free_vars for v in free_vars(aa))]
            depth = (sv_depth - 1) if isinstance(e, EStateVar) else sv_depth
            pool = STATE_POOL if depth else RUNTIME_POOL
            cost = self.cost_model.cost(e, pool)
            info = (e, r, cost, a, pool, bound)
            self.watched_exps.append(info)
            self.behavior_index.put(e, EAll(a), self.all_examples, info)
        self.fix_seen()

    def _examples_for(self, e):
        # binders = [b for b in free_vars(e) if b in self.binders]
        # return instantiate_examples((self.target,), self.examples, self.binders)
        return self.all_examples

    def _fingerprint(self, e):
        return fingerprint(e, self._examples_for(e))

    def _doctor_for_context(self, e : Exp, bound_vars : {EVar}):
        """
        Fix an expression so that it has no bad free variables.

        Binders are not allowed to be free in output expressions. Since no
        binders are free in the input expression, it is actually OK to replace
        them with arbitrary expressions of the correct type without affecting
        correctness.

        In order to ensure that the synthesizer continues to make progress, we
        pull the "arbitrary expression" from the set of things we have seen the
        value get bound to in the past. If the binder is incorrect here, then
        the verifier will produce a counterexample in which it gets bound to
        something else.
        """
        value_by_var = { }
        eval_bulk(self.target, self.examples, bind_callback=lambda var, val: value_by_var.update({var:val}))
        v = find_one(fv for fv in free_vars(e) if fv in self.binders and fv not in bound_vars)
        while v:
            e = subst(e, { v.id : uneval(v.type, value_by_var.get(v, mkval(v.type))) })
            v = find_one(fv for fv in free_vars(e) if fv in self.binders and fv not in bound_vars)
        return e

    def _possible_replacements(self, e, pool, cost, fp):
        """
        Yields watched expressions that appear as worse versions of the given
        expression. There may be more than one.
        """
        for (watched_e, r, watched_cost, assumptions, p, bound) in self.behavior_index.search(fp):
            if p != pool:
                continue
            if watched_cost < cost:
                continue
            e2 = self._doctor_for_context(e, bound)
            if e != e2:
                print("*** doctoring took place; ctx=[{}]".format(", ".join(v.id for v in bound)))
                print("    original --> {}".format(pprint(e)))
                print("    modified --> {}".format(pprint(e2)))
            if e2 == watched_e:
                continue
            yield (watched_e, e2, r)

    def next(self):
        while True:
            if self.backlog is not None:
                improvements = list(self._possible_replacements(*self.backlog))
                if self.backlog_counter < len(improvements):
                    i = improvements[self.backlog_counter]
                    self.backlog_counter += 1
                    return i
                else:
                    self.backlog = None
                    self.backlog_counter = 0
            for (e, pool) in self.builder_iter:
                if self.stop_callback():
                    raise StopException()

                cost = self.cost_model.cost(e, pool)

                if (self.cost_model.is_monotonic() or hyperaggressive_culling.value) and cost > self.cost_ceiling:
                    _on_exp(e, "too expensive", cost, self.cost_ceiling)
                    continue

                fp = self._fingerprint(e)
                prev = self.seen.get((pool, fp))

                if prev is None:
                    self.seen[(pool, fp)] = (cost, [(e, self.current_size)])
                    self.cache.add(e, pool=pool, size=self.current_size)
                    self.last_progress = self.current_size
                    _on_exp(e, "new", "runtime" if pool == RUNTIME_POOL else "state")
                else:
                    prev_cost, prev_exps = prev
                    if enforce_strong_progress.value:
                        bad = find_one(all_exps(e), lambda ee: any(alpha_equivalent(ee, pe) for pe in prev_exps))
                        if bad:
                            _on_exp(e, "failed strong progress requirement", bad)
                            continue
                    if any(alpha_equivalent(e, ee) for (ee, size) in prev_exps):
                        _on_exp(e, "duplicate")
                        continue
                    elif cost == prev_cost:
                        self.cache.add(e, pool=pool, size=self.current_size)
                        self.seen[(pool, fp)][1].append((e, self.current_size))
                        self.last_progress = self.current_size
                        _on_exp(e, "equivalent", *[e for (e, cost) in prev_exps])
                    elif cost < prev_cost:
                        for (prev_exp, prev_size) in prev_exps:
                            self.cache.evict(prev_exp, size=prev_size, pool=pool)
                            if (self.cost_model.is_monotonic() or hyperaggressive_culling.value) and hyperaggressive_eviction.value:
                                for (cached_e, size, p) in list(self.cache):
                                    if p != pool:
                                        continue
                                    if prev_exp in all_exps(cached_e):
                                        _on_exp(cached_e, "evicted since it contains", prev_exp)
                                        self.cache.evict(cached_e, size=size, pool=pool)
                        self.cache.add(e, pool=pool, size=self.current_size)
                        self.seen[(pool, fp)] = (cost, [(e, self.current_size)])
                        self.last_progress = self.current_size
                        _on_exp(e, "better", *[e for (e, cost) in prev_exps])
                    else:
                        _on_exp(e, "worse", *[e for (e, cost) in prev_exps])
                        continue

                improvements = list(self._possible_replacements(e, pool, cost, fp))
                if improvements:
                    self.backlog = (e, pool, cost, fp)
                    self.backlog_counter = 1
                    return improvements[0]

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
                    # print("No legal binder to use for {}".format(e))
                    return ELambda(e.arg, self.visit(e.body))
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
        for (e, pool) in self.wrapped_builder.build(cache, size):
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

            yield (e, pool)

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

_DONE = set([EVar, EEnumEntry, ENum, EStr, EBool])
def heuristic_done(e : Exp, args : [EVar] = []):
    return (
        (type(e) in _DONE) or
        (isinstance(e, ESingleton) and heuristic_done(e.e)) or
        (isinstance(e, EStateVar) and heuristic_done(e.e)))

def never_stop():
    return False

@typechecked
def improve(
        target : Exp,
        assumptions : Exp,
        binders : [EVar],
        args : [EVar],
        cost_model : CostModel,
        builder : ExpBuilder,
        stop_callback = never_stop,
        hints : [Exp] = None,
        examples = None):
    """
    Improve the target expression using enumerative synthesis.
    This function is a generator that yields increasingly better and better
    versions of the input expression `target`.

    Notes on internals of this algorithm follow.

    Key differences from "regular" enumerative synthesis:
        - Expressions may be built using a set of "binders"---extra free
          variables thrown into the mix at the beginning.
        - Expressions are either "state" expressions or "runtime" expressions,
          allowing this algorithm to choose what things to store on the data
          structure and what things to compute at query execution time. (The
          cost model is ultimately responsible for this choice.)

    Other features of this algorithm:
        - If a better version of *any subexpression* for the target is found,
          it is immediately substituted in and the overall expression is
          returned. This "smooths out" the search space a little, and lets us
          find kinda-good solutions very quickly, even if the best possible
          solution is out of reach.
    """

    print("call to improve:")
    print("""improve(
        target={target!r},
        assumptions={assumptions!r},
        binders={binders!r},
        args={args!r},
        cost_model={cost_model!r},
        builder={builder!r},
        stop_callback={stop_callback!r},
        hints={hints!r},
        examples={examples!r})""".format(
            target=target,
            assumptions=assumptions,
            binders=binders,
            args=args,
            cost_model=cost_model,
            builder=builder,
            stop_callback=stop_callback,
            hints=hints,
            examples=examples))

    print()
    print("improving: {}".format(pprint(target)))
    print("subject to: {}".format(pprint(assumptions)))
    print()

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
    learner = Learner(target, assumptions, binders, args, vars + binders, examples, cost_model, builder, stop_callback)
    try:
        while True:
            # 1. find any potential improvement to any sub-exp of target
            try:
                old_e, new_e, repl = learner.next()
            except NoMoreImprovements:
                break

            # 2. substitute-in the improvement
            print("Found candidate replacement [{}] for [{}] in".format(pprint(new_e), pprint(old_e)))
            print(pprint(repl(EVar("@___"))))
            new_target = repl(new_e)

            assert not find_one(free_vars(new_target), lambda v: v not in vars)

            # 3. check
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
                old_cost = cost_model.cost(target, RUNTIME_POOL)
                new_cost = cost_model.cost(new_target, RUNTIME_POOL)
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
                            f.write("    if costmodel.cost(new_e, RUNTIME_POOL) <= costmodel.cost(old_e, RUNTIME_POOL) and costmodel.cost(new_target, RUNTIME_POOL) > costmodel.cost(target, RUNTIME_POOL):\n")
                            f.write('        for name, x in zip(["old_e", "new_e", "target", "new_target"], [old_e, new_e, target, new_target]):\n')
                            f.write('            print("{}: {}".format(name, pprint(x)))\n')
                            f.write('            print("    cost = {}".format(costmodel.cost(x, RUNTIME_POOL)))\n')
                            f.write("        assert False\n")
                    # raise Exception("detected nonmonotonicity")
                    continue
                if new_cost == old_cost:
                    print("...but cost ({}) is unchanged".format(old_cost))
                    continue
                print("found improvement: {} -----> {}".format(pprint(old_e), pprint(new_e)))
                print("cost: {} -----> {}".format(old_cost, new_cost))
                if reset_on_success.value:
                    learner.reset(examples, update_watched_exps=False)
                learner.watch(new_target, assumptions)
                target = new_target
                yield new_target

                if heuristic_done(new_target, args):
                    print("target now matches doneness heuristic")
                    break

    except KeyboardInterrupt:
        for e in learner.cache.random_sample(50):
            print(pprint(e))
        raise
