from collections import defaultdict, OrderedDict
import datetime
import itertools
import functools
import sys
import traceback

from cozy.target_syntax import *
from cozy.typecheck import is_collection
from cozy.syntax_tools import subst, pprint, free_vars, free_funcs, BottomUpExplorer, BottomUpRewriter, equal, fresh_var, alpha_equivalent, all_exps, implies, mk_lambda, enumerate_fragments, strip_EStateVar
from cozy.wf import ExpIsNotWf, exp_wf, exp_wf_nonrecursive
from cozy.common import OrderedSet, ADT, Visitor, fresh_name, unique, pick_to_sum, cross_product, OrderedDefaultDict, OrderedSet, group_by, find_one, extend
from cozy.solver import satisfy, satisfiable, valid, IncrementalSolver
from cozy.evaluation import eval, eval_bulk, mkval, construct_value, uneval, eq
from cozy.cost_model import CostModel, Cost, CompositeCostModel
from cozy.opts import Option
from cozy.pools import ALL_POOLS, RUNTIME_POOL, STATE_POOL, pool_name

from .acceleration import try_optimize

eliminate_vars = Option("eliminate-vars", bool, True)
reset_on_success = Option("reset-on-success", bool, False)
check_depth = Option("proof-depth", int, 4)
incremental = Option("incremental", bool, False, description="Experimental option that can greatly improve performance.")
check_final_cost = Option("check-final-cost", bool, True)

class StopException(Exception):
    pass

class NoMoreImprovements(Exception):
    pass

class Learner(object):
    def __init__(self, target, assumptions, state_vars, args, legal_free_vars, examples, cost_model, stop_callback, hints, solver):
        self.state_vars = OrderedSet(state_vars)
        self.args = OrderedSet(args)
        self.stop_callback = stop_callback
        self.cost_model = cost_model
        self.assumptions = assumptions
        self.hints = list(hints)
        self.reset(examples)
        self.watch(target)

    def reset(self, examples):
        self.examples = list(examples)

    def watch(self, new_target):
        self.target = new_target

    def matches(self, fp, target_fp):
        assert isinstance(fp[0], Type)
        assert isinstance(target_fp[0], Type)
        if fp[0] != target_fp[0]:
            return False
        t = fp[0]
        return all(eq(t, fp[i], target_fp[i]) for i in range(1, len(fp)))

    def next(self):
        class No(object):
            def __init__(self, msg):
                self.msg = msg
            def __bool__(self):
                return False
            def __str__(self):
                return "no: {}".format(self.msg)
        cards = [self.cost_model.cardinality(ctx.e) for ctx in enumerate_fragments(self.target) if is_collection(ctx.e.type)]
        def check_wf(e, ctx, pool):
            try:
                exp_wf(e, pool=pool, state_vars=self.state_vars, args=self.args, assumptions=self.assumptions)
            except ExpIsNotWf as exc:
                return No("at {}: {}".format(pprint(exc.offending_subexpression), exc.reason))
            if isinstance(e.type, TBag):
                c = self.cost_model.cardinality(e)
                if all(cc < c for cc in cards):
                    # print("too big: {}".format(pprint(e)))
                    return No("too big")
            return True

        from cozy.enumeration import Enumerator, fingerprint
        from cozy.contexts import RootCtx, shred, replace

        root_ctx = RootCtx(state_vars=self.state_vars, args=self.args)
        frags = list(unique(shred(self.target, root_ctx)))
        enum = Enumerator(
            examples=self.examples,
            cost_model=self.cost_model,
            check_wf=check_wf,
            hints=frags,
            heuristics=try_optimize)

        size = 0
        target_cost = self.cost_model.cost(self.target, RUNTIME_POOL)
        target_fp = fingerprint(self.target, self.examples)

        if not hasattr(self, "blacklist"):
            self.blacklist = set()

        while True:

            print("starting minor iteration {} with |cache|={}".format(size, enum.cache_size()))

            n = 0
            for (e, ctx, pool) in frags:
                for info in enum.enumerate_with_info(size=size, context=ctx, pool=pool):
                    if self.stop_callback():
                        raise StopException()
                    if info.e.type != e.type:
                        continue
                    if alpha_equivalent(info.e, e):
                        continue

                    k = (e, ctx, pool, info.e)
                    if k in self.blacklist:
                        continue
                    self.blacklist.add(k)

                    n += 1
                    ee = replace(
                        self.target, root_ctx, RUNTIME_POOL,
                        e, ctx, pool,
                        info.e)
                    if not check_wf(ee, root_ctx, RUNTIME_POOL):
                        continue
                    if not self.matches(fingerprint(ee, self.examples), target_fp):
                        continue
                    if self.cost_model.cost(ee, RUNTIME_POOL).compare_to(target_cost) != Cost.BETTER:
                        continue
                    print("FOUND A GUESS AFTER {} CONSIDERED".format(n))
                    return ee

            print("CONSIDERED {}".format(n))
            size += 1

        raise NoMoreImprovements()

def exp_is_wf(e, pool, state_vars, args, assumptions):
    try:
        exp_wf(e, state_vars, args, pool, assumptions=assumptions)
    except ExpIsNotWf as exc:
        return False
    return True

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
        (isinstance(e, EUnaryOp) and e.op == "-" and heuristic_done(e.e)) or
        (isinstance(e, ENull)))

def never_stop():
    return False

def improve(
        target        : Exp,
        state_vars    : [EVar],
        args          : [EVar],
        assumptions   : Exp            = T,
        cost_model    : CostModel      = None,
        stop_callback                  = never_stop,
        hints         : [Exp]          = (),
        examples      : [{str:object}] = ()):
    """
    Improve the target expression using enumerative synthesis.
    This function is a generator that yields increasingly better and better
    versions of the input expression `target`.

    Notes on internals of this algorithm follow.

    Key differences from "regular" enumerative synthesis:
        - Expressions are either "state" expressions or "runtime" expressions,
          allowing this algorithm to choose what things to store on the data
          structure and what things to compute at query execution time. (The
          cost model is ultimately responsible for this choice.)
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
        state_vars={state_vars!r},
        args={args!r},
        cost_model={cost_model!r},
        stop_callback={stop_callback!r},
        hints={hints!r},
        examples={examples!r})""".format(
            target=target,
            assumptions=assumptions,
            state_vars=state_vars,
            args=args,
            cost_model=cost_model,
            stop_callback=stop_callback,
            hints=hints,
            examples=examples))

    print()
    print("improving: {}".format(pprint(target)))
    print("subject to: {}".format(pprint(assumptions)))
    print()

    try:
        assert exp_wf(
            target,
            state_vars=set(state_vars),
            args=set(args),
            assumptions=assumptions)
    except ExpIsNotWf as ex:
        print("WARNING: initial target is not well-formed [{}]; this might go poorly...".format(str(ex)))
        print(pprint(ex.offending_subexpression))
        print(pprint(ex.offending_subexpression.type))
        # raise

    # Bit of a hack, but... a CompositeCostModel needs to be initialized with
    # the proper assumptions.  It also needs to be local to the synthesis task,
    # since it is stateful.  This safely prevents misuse by clients.
    if cost_model is None or isinstance(cost_model, CompositeCostModel):
        cost_model = CompositeCostModel(assumptions=assumptions)

    target_cost = cost_model.cost(target, RUNTIME_POOL)

    if eliminate_vars.value and can_elim_vars(target, assumptions, state_vars):
        print("This job does not depend on state_vars.")
        # TODO: what can we do about it?

    vars = list(free_vars(target) | free_vars(assumptions) | set(args) | set(state_vars))
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

    examples = list(examples)
    learner = Learner(target, assumptions, state_vars, args, vars, examples, cost_model, stop_callback, hints, solver=solver)
    try:
        while True:
            # 1. find any potential improvement to any sub-exp of target
            try:
                new_target = learner.next()
            except NoMoreImprovements:
                break
            print("Found candidate improvement: {}".format(pprint(new_target)))

            # 2. check
            if incremental.value:
                solver.push()
                solver.add_assumption(ENot(EBinOp(target, "==", new_target).with_type(BOOL)))
                counterexample = _sat(T)
            else:
                formula = EAll([assumptions, ENot(EBinOp(target, "==", new_target).with_type(BOOL))])
                counterexample = _sat(formula)
            if counterexample is not None:
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

                if check_final_cost.value:
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
                print("The improvement is valid!")
                # print(repr(target))
                # print(repr(new_target))

                yield new_target

                if reset_on_success.value and (not check_final_cost.value or ordering != Cost.UNORDERED):
                    learner.reset(examples)
                learner.watch(new_target)
                target = new_target

                if heuristic_done(new_target, args):
                    print("target now matches doneness heuristic")
                    break
            if incremental.value:
                solver.pop()

    except KeyboardInterrupt:
        raise
