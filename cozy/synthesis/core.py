from collections import defaultdict, OrderedDict
import datetime
import itertools
import sys
import traceback

from cozy.target_syntax import *
from cozy.syntax_tools import subst, pprint, free_vars, free_funcs, BottomUpExplorer, BottomUpRewriter, equal, fresh_var, alpha_equivalent, all_exps, implies, mk_lambda, enumerate_fragments2, strip_EStateVar
from cozy.wf import ExpIsNotWf, exp_wf, exp_wf_nonrecursive
from cozy.common import OrderedSet, ADT, Visitor, fresh_name, typechecked, unique, pick_to_sum, cross_product, OrderedDefaultDict, OrderedSet, group_by, find_one
from cozy.solver import satisfy, satisfiable, valid, IncrementalSolver
from cozy.evaluation import eval, eval_bulk, mkval, construct_value, uneval
from cozy.cost_model import CostModel, Cost
from cozy.opts import Option
from cozy.pools import ALL_POOLS, RUNTIME_POOL, STATE_POOL, pool_name

from .cache import Cache, SeenSet

save_testcases = Option("save-testcases", str, "", metavar="PATH")
hyperaggressive_culling = Option("hyperaggressive-culling", bool, False)
hyperaggressive_eviction = Option("hyperaggressive-eviction", bool, True)
reject_symmetric_binops = Option("reject-symmetric-binops", bool, False)
eliminate_vars = Option("eliminate-vars", bool, True)
reset_on_success = Option("reset-on-success", bool, False)
enforce_exprs_wf = Option("enforce-expressions-well-formed", bool, False)
preopt = Option("optimize-accelerated-exps", bool, True)
check_depth = Option("proof-depth", int, 4)
incremental = Option("incremental", bool, False, description="Experimental option that can greatly improve performance.")

# When are costs checked?
CHECK_FINAL_COST = True  # compare overall cost of each candidiate to target

class ExpBuilder(object):
    def check(self, e, pool):
        if enforce_exprs_wf.value:
            from cozy.typecheck import retypecheck
            assert retypecheck(e)
        return (e, pool)
    def build(self, cache, size):
        raise NotImplementedError()

def instantiate_examples(examples, binders : [EVar]):
    res = []
    for ex in examples:
        ex = dict(ex)
        for b in binders:
            if b.id not in ex:
                ex[b.id] = mkval(b.type)
        res.append(ex)
    return res

def fingerprint(e, examples):
    return (e.type,) + tuple(eval_bulk(e, examples))

class StopException(Exception):
    pass

class NoMoreImprovements(Exception):
    pass

oracle = EFilter(EVar("groups"), ELambda(EVar("x"), EEq(EGetField(EGetField(EVar("x"), "val"), "rosterMode"), EEnumEntry("EVERYBODY"))))
_fates = defaultdict(int)
def _on_exp(e, fate, *args):
    _fates[fate] += 1
    return
    outfile = sys.stdout
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
    # if True:
    # if "expensive" in fate:
        print(" ---> [{}, {}] {}; {}".format(fate, pprint(e.type), pprint(e), ", ".join((pprint(e) if isinstance(e, ADT) else str(e)) for e in args)), file=outfile)

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

class SpecDependentBuilder(ExpBuilder):
    def watch(self, new_target):
        raise NotImplementedError()

class SubstitutingBuilder(SpecDependentBuilder):
    def __init__(self, wrapped, binders=(), target=None):
        self.wrapped = wrapped
        self.binders = OrderedSet(binders)
        self.watch(target)
    def watch(self, new_target):
        if isinstance(self.wrapped, SpecDependentBuilder):
            self.wrapped.watch(new_target)
        if new_target is None:
            self._watches = {}
            return
        self._watches = group_by(
            enumerate_fragments2(new_target),
            k=lambda ctx: (ctx.pool, ctx.e.type),
            v=lambda ctxs: sorted(ctxs, key=lambda ctx: -ctx.e.size()))
    def build(self, cache, size):
        for pool in ALL_POOLS:
            for e in cache.find(pool=pool, size=size-1):
                free_binders = OrderedSet(v for v in free_vars(e) if v in self.binders)
                for ctx in self._watches.get((pool, e.type), ()):
                    assert e.type == ctx.e.type
                    assert pool == ctx.pool
                    if e == ctx.e:
                        continue
                    unbound_binders = [b for b in free_binders if b not in ctx.bound_vars]
                    if unbound_binders:
                        _on_exp(e, "skipped replacement with free binders", ", ".join(b.id for b in unbound_binders))
                        continue
                    ee = ctx.replace_e_with(e)
                    # TODO: it might be a good idea to either
                    #  (1) never cache expressions yielded here or
                    #  (2) only cache expressions if they reduce the total size
                    # ee._cache = False
                    ee._fullcheck = True
                    yield self.check(ee, RUNTIME_POOL)
        yield from self.wrapped.build(cache, size)

class StealingBuilder(SpecDependentBuilder):
    def __init__(self, wrapped, state_vars, args, assumptions, target=None):
        self.wrapped = wrapped
        self.state_vars = OrderedSet(state_vars)
        self.args = OrderedSet(args)
        self.assumptions = assumptions
        self.watch(target)
    def watch(self, new_target):
        if isinstance(self.wrapped, SpecDependentBuilder):
            self.wrapped.watch(new_target)
        self.target = new_target
    def is_legal_in_pool(self, e, pool):
        try:
            return exp_wf(e, state_vars=self.state_vars, args=self.args, pool=pool, assumptions=self.assumptions)
        except ExpIsNotWf as exc:
            return False
    def check(self, e, pool):
        _on_exp(e, "new root", pool_name(pool))
        e._root = False
        for a in ("_accel", "_cache"):
            if hasattr(e, a):
                delattr(e, a)
        return super().check(e, pool)
    def build(self, cache, size):
        if size == 0 and self.target is not None:
            for e in all_exps(self.target):
                if isinstance(e, ELambda):
                    continue
                for pool in ALL_POOLS:
                    x = strip_EStateVar(e) if pool == STATE_POOL else e
                    if self.is_legal_in_pool(x, pool):
                        yield self.check(x, pool)
                        if pool == STATE_POOL:
                            ee = EStateVar(x).with_type(x.type)
                            if self.is_legal_in_pool(ee, RUNTIME_POOL):
                                yield self.check(ee, RUNTIME_POOL)
        yield from self.wrapped.build(cache, size)

class Learner(object):
    def __init__(self, target, assumptions, binders, state_vars, args, legal_free_vars, examples, cost_model, builder, stop_callback, hints, solver):
        self.binders = OrderedSet(binders)
        self.state_vars = OrderedSet(state_vars)
        self.args = OrderedSet(args)
        self.legal_free_vars = legal_free_vars
        self.stop_callback = stop_callback
        self.cost_model = cost_model
        self.builder = builder
        self.builder = StealingBuilder(self.builder, state_vars=state_vars, args=args, assumptions=assumptions, target=target)
        self.builder = SubstitutingBuilder(self.builder, binders=binders, target=target)
        self.builder = FixedBuilder(self.builder, state_vars, args, binders, assumptions)
        self.seen = SeenSet()
        self.assumptions = assumptions
        self.hints = list(hints)
        self.solver = solver
        self.reset(examples)
        self.watch(target)

    def compare_costs(self, c1, c2):
        self.ccount += 1
        solver = self.solver
        if solver is not None:
            return c1.compare_to(c2, solver=solver)
        else:
            return c1.compare_to(c2, assumptions=self.assumptions)

    def reset(self, examples):
        self.cache = Cache(binders=self.binders, args=self.args)
        self.current_size = -1
        self.examples = list(examples)
        self.all_examples = instantiate_examples(self.examples, self.binders)
        self.seen.clear()
        self.builder_iter = ()
        self.last_progress = 0
        self._start_minor_it()

    def watch(self, new_target):
        self.target = new_target
        self.builder.watch(new_target)

    def _fingerprint(self, e):
        self.fpcount += 1
        # bs = tuple(sorted(free_vars(e) & self.binders))
        bs = (len(free_vars(e) & self.binders),)
        return bs + fingerprint(e, self.all_examples)

    def pre_optimize(self, e, pool):
        """
        Optimize `e` by replacing its subexpressions with the best cached
        versions available (or leaving them untouched if they are new).
        """
        if not hasattr(e, "_accel"):
            return e
        top_level = e
        class V(BottomUpRewriter):
            def visit_EStateVar(_, e):
                return EStateVar(self.pre_optimize(e.e, STATE_POOL)).with_type(e.type)
            def visit_ELambda(_, e):
                if e.arg not in self.binders and e.arg in free_vars(e.body):
                    # Derp!  Someone made an expression that uses an illegal
                    # binder.  There is no way to compute a fingerprint for the
                    # body, unfortunately, so we just stop here.
                    return e
                return ELambda(e.arg, super().visit_ADT(e.body)) # optimize children
            def visit_Exp(_, e): # do not shadow `self`
                if e is top_level:
                    return super().visit_ADT(e) # optimize children
                fp = self._fingerprint(e)
                prev = self.seen.find_one(pool, fp)
                if prev is None:
                    return super().visit_ADT(e) # optimize children
                prev_exp, prev_size, prev_cost = prev
                if prev_exp == e:
                    return prev_exp
                cost = self.cost_model.cost(e, pool)
                ordering = self.compare_costs(cost, prev_cost)
                if ordering == Cost.BETTER:
                    return super().visit_ADT(e) # optimize children
                else:
                    # NOTE: no need to optimize children; if it is cached, then
                    # it is presumably already the best possible.
                    # if not alpha_equivalent(e, prev_exp):
                    #     print("*** rewriting {} to {}".format(pprint(e), pprint(prev_exp)), file=sys.stderr)
                    return prev_exp
        res = None
        try:
            res = V().visit(e)
            assert exp_wf(res, state_vars=self.state_vars, args=self.args, pool=pool, assumptions=self.assumptions)
            if hasattr(e, "_tag"):
                res._tag = e._tag
            return res
        except Exception as ex:
            # traceback.print_exc(file=sys.stdout)
            print("FAILED TO PREOPTIMIZE [exn={}] {} ---> {}".format(ex, pprint(e), pprint(res)))
            # print(repr(e))
            return e

    def _start_minor_it(self):
        now = datetime.datetime.now()
        if _fates:
            for f, ct in sorted(_fates.items(), key=lambda x: x[1], reverse=True):
                print("  {:6} | {}".format(ct, f))
            _fates.clear()
        if hasattr(self, "mstart"):
            duration = now - self.mstart
            print("> minor duration:   {}".format(duration))
            print("> next() calls:     {}".format(self.ncount))
            print("> total exps:       {}".format(self.ecount))
            print("> exps/s:           {}".format(self.ecount / duration.total_seconds()))
            print("> cost comparisons: {}".format(self.ccount))
            print("> fingerprints:     {}".format(self.fpcount))
        if self.current_size >= 0:
            print("minor iteration {}, |cache|={}".format(self.current_size, len(self.cache)))
        self.mstart = now
        self.ecount = 0
        self._ecount = 0
        self.ccount = 0
        self.fpcount = 0
        self.ncount = 0

    def _on_exp(self, e, pool):
        # print("*** ", end="")
        # print(pprint(e))
        now = datetime.datetime.now()
        if not hasattr(self, "_on_exp_time"):
            self._on_exp_time = now
            self._ecount = 0
        elapsed = now - self._on_exp_time
        if elapsed > datetime.timedelta(seconds=30):
            print("... exps/s: {:.1f}".format(self._ecount / elapsed.total_seconds()))
            self._on_exp_time = now
            self._ecount = 0
        self._ecount += 1
        self.ecount += 1

    def matches(self, fp, target_fp):
        assert isinstance(fp[0], int)
        assert isinstance(fp[1], Type)
        assert len(fp) == len(target_fp)
        if fp[0] != target_fp[0] or fp[1] != target_fp[1]:
            return False
        t = fp[1]
        assert isinstance(t, Type)
        from cozy.evaluation import eq
        return all(eq(t, fp[i], target_fp[i]) for i in range(2, len(fp)))

    def next(self):
        target_cost = self.cost_model.cost(self.target, RUNTIME_POOL)
        target_fp = self._fingerprint(self.target)
        self.ncount += 1
        while True:
            for (e, pool) in self.builder_iter:
                self._on_exp(e, pool)
                if self.stop_callback():
                    raise StopException()

                new_e = self.pre_optimize(e, pool) if preopt.value else e
                if new_e is not e:
                    _on_exp(e, "preoptimized", new_e)
                    e = new_e

                cost = self.cost_model.cost(e, pool)

                if pool == RUNTIME_POOL and (self.cost_model.is_monotonic() or hyperaggressive_culling.value) and self.compare_costs(cost, target_cost) == Cost.WORSE:
                    _on_exp(e, "too expensive", cost, target_cost)
                    continue

                fp = self._fingerprint(e)
                prev = list(self.seen.find_all(pool, fp))
                should_add = True
                if not prev:
                    _on_exp(e, "new", pool_name(pool))
                elif any(alpha_equivalent(e, ee) for (ee, _, _) in prev):
                    _on_exp(e, "duplicate")
                    should_add = False
                else:
                    better_than = None
                    worse_than = None
                    for prev_exp, prev_size, prev_cost in prev:
                        ordering = self.compare_costs(cost, prev_cost)
                        assert ordering in (Cost.WORSE, Cost.BETTER, Cost.UNORDERED)
                        _on_exp(e, ordering, pool_name(pool), prev_exp)
                        if ordering == Cost.UNORDERED:
                            continue
                        elif ordering == Cost.BETTER:
                            better_than = (prev_exp, prev_size, prev_cost)
                            _on_exp(prev_exp, "found better alternative", e)
                            self.cache.evict(prev_exp, size=prev_size, pool=pool)
                            self.seen.remove(prev_exp, pool, fp)
                            if (self.cost_model.is_monotonic() or hyperaggressive_culling.value) and hyperaggressive_eviction.value:
                                for (cached_e, size, p) in list(self.cache):
                                    if p != pool:
                                        continue
                                    if prev_exp in all_exps(cached_e):
                                        _on_exp(cached_e, "evicted since it contains", prev_exp)
                                        self.cache.evict(cached_e, size=size, pool=pool)
                        else:
                            should_add = False
                            worse_than = (prev_exp, prev_size, prev_cost)
                            # break
                    if worse_than and better_than:
                        print("Uh-oh! Strange cost relationship between")
                        print("  (1) this exp: {}".format(pprint(e)))
                        print("  (2) prev. A:  {}".format(pprint(worse_than[0])))
                        print("  (2) prev. B:  {}".format(pprint(better_than[0])))
                        print("e1 = {}".format(repr(e)))
                        print("e2 = {}".format(repr(worse_than[0])))
                        print("e3 = {}".format(repr(better_than[0])))
                        print("(1) vs (2): {}".format(cost.compare_to(worse_than[2], self.assumptions)))
                        print("(2) vs (3): {}".format(worse_than[2].compare_to(better_than[2], self.assumptions)))
                        print("(3) vs (1): {}".format(better_than[2].compare_to(cost, self.assumptions)))
                        # raise Exception("insane cost model behavior")

                if should_add:
                    self.cache.add(e, pool=pool, size=self.current_size)
                    self.seen.add(e, pool, fp, self.current_size, cost)
                    self.last_progress = self.current_size
                else:
                    continue

                if pool == RUNTIME_POOL and self.matches(fp, target_fp) and e != self.target:
                    return (self.target, e, (), lambda x: x)

            if self.last_progress < (self.current_size+1) // 2:
                raise NoMoreImprovements("hit termination condition")

            self.current_size += 1
            self.builder_iter = self.builder.build(self.cache, self.current_size)
            self._start_minor_it()

@typechecked
def fixup_binders(e : Exp, binders_to_use : [EVar], allow_add=False, throw=False) -> Exp:
    binders_by_type = group_by(binders_to_use, lambda b: b.type)
    class V(BottomUpRewriter):
        def visit_ELambda(self, e):
            if e.arg in binders_by_type[e.arg.type]:
                return super().visit_ADT(e)
            fvs = free_vars(e.body)
            legal_repls = [ b for b in binders_by_type[e.arg.type] if b not in fvs ]
            if not legal_repls:
                if allow_add:
                    print("Adding aux binder {} and returning {}".format(e.arg, pprint(ELambda(e.arg, e.body))), file=sys.stderr)
                    binders_to_use.append(e.arg)
                    binders_by_type[e.arg.type].append(e.arg)
                    return ELambda(e.arg, self.visit(e.body))
                else:
                    if throw:
                        print("No legal binder to use for {}".format(pprint(e)))
                        raise Exception(pprint(e))
                    else:
                        return ELambda(e.arg, self.visit(e.body))
            b = legal_repls[0]
            return ELambda(b, self.visit(subst(e.body, { e.arg.id : b })))
    return V().visit(e)

COMMUTATIVE_OPERATORS = set(("==", "and", "or", "+"))
ATTRS_TO_PRESERVE = ("_accel", "_tag", "_fullcheck")

class FixedBuilder(ExpBuilder):
    def __init__(self, wrapped_builder, state_vars, args, binders_to_use, assumptions : Exp):
        self.wrapped_builder = wrapped_builder
        self.state_vars = OrderedSet(state_vars)
        self.args = OrderedSet(args)
        self.binders_to_use = binders_to_use
        self.assumptions = assumptions
    def watch(self, new_target):
        if isinstance(self.wrapped_builder, SpecDependentBuilder):
            self.wrapped_builder.watch(new_target)
    def build(self, cache, size):
        for (e, pool) in self.wrapped_builder.build(cache, size):
            try:
                orig = e
                e = fixup_binders(e, self.binders_to_use)
                for a in ATTRS_TO_PRESERVE:
                    if hasattr(orig, a):
                        setattr(e, a, getattr(orig, a))
            except Exception:
                _on_exp(e, "unable to rename binders")
                continue
                print("WARNING: skipping built expression {}".format(pprint(e)), file=sys.stderr)

            if reject_symmetric_binops.value and size > 1 and isinstance(e, EBinOp) and e.op in COMMUTATIVE_OPERATORS and e.e2 < e.e1:
                _on_exp(e, "rejecting symmetric use of commutative operator")
                continue

            try:
                # Acceleration rules can produce arbitrary expressions, so we
                # need to recursively check them.  The regular grammar only
                # produces expressions "one level deep"---all subexpressions
                # have already been checked.
                if hasattr(e, "_accel") or hasattr(e, "_fullcheck"):
                    exp_wf(e, self.state_vars, self.args, pool, assumptions=self.assumptions)
                else:
                    exp_wf_nonrecursive(e, self.state_vars, self.args, pool, assumptions=self.assumptions)
            except ExpIsNotWf as exc:
                _on_exp(e, exc.reason, exc.offending_subexpression)
                continue

            yield (e, pool)

class StateElimBuilder(ExpBuilder):
    def __init__(self, wrapped_builder):
        self.wrapped_builder = wrapped_builder
    def build(self, cache, size):
        for tup in self.wrapped_builder.build(cache, size):
            e, pool = tup
            if pool != STATE_POOL and not any(isinstance(x, EStateVar) for x in all_exps(e)):
                yield tup
            else:
                _on_exp(e, "culled state expression")

def truncate(s):
    if len(s) > 60:
        return s[:60] + "..."
    return s

def can_elim_vars(spec : Exp, assumptions : Exp, vs : [EVar]):
    spec = strip_EStateVar(spec)
    sub = { v.id : fresh_var(v.type) for v in vs }
    return valid(EImplies(
        EAll([assumptions, subst(assumptions, sub)]),
        EEq(spec, subst(spec, sub))))

_DONE = set([EVar, EEnumEntry, ENum, EStr, EBool, EEmptyList, ENull])
def heuristic_done(e : Exp, args : [EVar] = []):
    return (
        (type(e) in _DONE) or
        (isinstance(e, ESingleton) and heuristic_done(e.e)) or
        (isinstance(e, EStateVar) and heuristic_done(e.e)) or
        (isinstance(e, EGetField) and heuristic_done(e.e)) or
        (isinstance(e, ENull)))

def never_stop():
    return False

@typechecked
def improve(
        target : Exp,
        assumptions : Exp,
        binders : [EVar],
        state_vars : [EVar],
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
        state_vars={state_vars!r},
        args={args!r},
        cost_model={cost_model!r},
        builder={builder!r},
        stop_callback={stop_callback!r},
        hints={hints!r},
        examples={examples!r})""".format(
            target=target,
            assumptions=assumptions,
            binders=binders,
            state_vars=state_vars,
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

    assert exp_wf(
        target,
        state_vars=set(state_vars),
        args=set(args),
        assumptions=assumptions)

    # Bit of a hack, but... a CompositeCostModel needs to be initialized with
    # the proper assumptions.  It also needs to be local to the synthesis task,
    # since it is stateful.  This safely prevents misuse by clients.
    from cozy.cost_model import CompositeCostModel
    if cost_model is None or isinstance(cost_model, CompositeCostModel):
        cost_model = CompositeCostModel(assumptions=assumptions)

    binders = list(binders)
    target = fixup_binders(target, binders, allow_add=False)
    hints = [fixup_binders(h, binders, allow_add=False) for h in (hints or ())]
    assumptions = fixup_binders(assumptions, binders, allow_add=False)
    target_cost = cost_model.cost(target, RUNTIME_POOL)

    if eliminate_vars.value and can_elim_vars(target, assumptions, state_vars):
        print("This job does not depend on state_vars.")
        builder = StateElimBuilder(builder)

    vars = list(free_vars(target) | free_vars(assumptions))
    funcs = free_funcs(EAll([target, assumptions]))

    solver = None
    if incremental.value:
        solver = IncrementalSolver(vars=vars, funcs=funcs, collection_depth=check_depth.value)
        solver.add_assumption(assumptions)
        _sat = solver.satisfy
    else:
        _sat = lambda e: satisfy(e, vars=vars, funcs=funcs, collection_depth=check_depth.value)

    if _sat(T) is None:
        print("assumptions are unsat; this query will never be called")
        yield construct_value(target.type)
        return

    if examples is None:
        examples = []
    learner = Learner(target, assumptions, binders, state_vars, args, vars + binders, examples, cost_model, builder, stop_callback, hints, solver=solver)
    try:
        while True:
            # 1. find any potential improvement to any sub-exp of target
            try:
                old_e, new_e, local_assumptions, repl = learner.next()
            except NoMoreImprovements:
                break

            # 2. substitute-in the improvement
            new_target = repl(new_e)
            print("Found candidate improvement: {}".format(pprint(new_target)))

            # 3. check
            if incremental.value:
                solver.push()
                solver.add_assumption(ENot(EBinOp(target, "==", new_target).with_type(BOOL)))
                counterexample = _sat(T)
            else:
                formula = EAll([assumptions, ENot(EBinOp(target, "==", new_target).with_type(BOOL))])
                counterexample = _sat(formula)
            if counterexample is not None:

                # Ok they aren't equal.  Now we need an example that
                # differentiates BOTH target/new_target AND old_e/new_e.
                if incremental.value:
                    counterexample = _sat(EAll([
                            EAll(local_assumptions),
                            ENot(EBinOp(old_e,  "===", new_e).with_type(BOOL))]))
                else:
                    counterexample = _sat(EAll([
                            assumptions,
                            EAll(local_assumptions),
                            ENot(EBinOp(target, "==", new_target).with_type(BOOL)),
                            ENot(EBinOp(old_e,  "===", new_e).with_type(BOOL))]))
                if counterexample is None:
                    print("!!! unable to satisfy top- and sub-expressions")
                    print("assumptions = {!r}".format(assumptions))
                    print("local_assumptions = {!r}".format(EAll(local_assumptions)))
                    print("old_e = {!r}".format(old_e))
                    print("target = {!r}".format(target))
                    print("new_e = {!r}".format(new_e))
                    print("new_target = {!r}".format(new_target))
                    raise Exception("unable to find an example that differentiates both the toplevel- and sub-expressions")

                if counterexample in examples:
                    print("assumptions = {!r}".format(assumptions))
                    print("duplicate example: {!r}".format(counterexample))
                    print("old target = {!r}".format(target))
                    print("new target = {!r}".format(new_target))
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

                if CHECK_FINAL_COST:
                    new_cost = cost_model.cost(new_target, RUNTIME_POOL)
                    print("cost: {} -----> {}".format(target_cost, new_cost))
                    if incremental.value:
                        ordering = new_cost.compare_to(target_cost, solver=solver)
                    else:
                        ordering = new_cost.compare_to(target_cost, assumptions=assumptions)
                    if ordering == Cost.WORSE:
                        # This should never happen, but to be safe...
                        print("*** cost is worse")
                        # print(repr(target))
                        # print(repr(new_target))
                        continue
                    elif ordering == Cost.UNORDERED:
                        print("*** cost is unchanged")
                        # print(repr(target))
                        # print(repr(new_target))
                        continue
                    target_cost = new_cost
                print("found improvement: {} -----> {}".format(pprint(old_e), pprint(new_e)))
                # print(repr(target))
                # print(repr(new_target))

                # binders are not allowed to "leak" out
                to_yield = new_target
                if any(v in binders for v in free_vars(new_target)):
                    print("WARNING: stripping binders in {}".format(pprint(new_target)), file=sys.stderr)
                    to_yield = subst(new_target, { b.id : construct_value(b.type) for b in binders })
                yield to_yield

                if reset_on_success.value and (not CHECK_FINAL_COST or ordering != Cost.UNORDERED):
                    learner.reset(examples)
                learner.watch(new_target)
                target = new_target

                if heuristic_done(new_target, args):
                    print("target now matches doneness heuristic")
                    break
            if incremental.value:
                solver.pop()

    except KeyboardInterrupt:
        for e in learner.cache.random_sample(50):
            print(pprint(e))
        raise
