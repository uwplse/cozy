"""Core synthesis algorithm for expressions.

The main function is `improve`, which takes an expression and yields
increasingly better and better versions of it.

There are a number of heuristics that affect how `improve` functions.
See their docstrings for more information.
 - exploration_order
 - hint_order
 - possibly_useful
 - heuristic_done
 - should_consider_replacement
"""

from collections import OrderedDict, namedtuple
import itertools
from typing import Callable

from multiprocessing import Value

from cozy import random_assignment
from cozy.syntax import (
    INT, BOOL, TMap,
    Op,
    Exp, ETRUE, ONE, EVar, ENum, EStr, EBool, EEmptyList, ESingleton, ELen, ENull,
    EAll, ENot, EImplies, EEq, EGt, ELe, ECond, EEnumEntry, EGetField,
    EBinOp, EUnaryOp, UOp, EArgMin, EArgMax, ELambda)
from cozy.target_syntax import (
    EFlatMap, EFilter, EMakeMap2, EStateVar,
    EDropFront, EDropBack)
from cozy.typecheck import is_collection, is_scalar
from cozy.syntax_tools import subst, pprint, free_vars, fresh_var, alpha_equivalent, strip_EStateVar, freshen_binders, wrap_naked_statevars, break_conj, inline_lets
from cozy.wf import exp_wf
from cozy.common import No, unique, OrderedSet, StopException
from cozy.solver import valid, solver_for_context, ModelCachingSolver
from cozy.evaluation import construct_value
from cozy.cost_model import CostModel, Order, LINEAR_TIME_UOPS
from cozy.opts import Option
from cozy.pools import Pool, RUNTIME_POOL, STATE_POOL, pool_name
from cozy.contexts import Context, all_subexpressions_with_context_information, replace
from cozy.logging import task, event
from cozy.structures import extension_handler

from .acceleration import try_optimize
from .enumeration import Enumerator, Fingerprint, retention_policy

eliminate_vars = Option("eliminate-vars", bool, False)
enable_blacklist = Option("enable-blacklist", bool, False,
    description='If enabled, skip expressions that have been ' +
                'found not useful or invalid during improvement searching')
check_blind_substitutions = Option("blind-substitutions", bool, True,
    description='"Blind substitutions" allow Cozy to try replacing expressions '
        + "with other expressions, even when the substitution appears wrong. "
        + "In some cases, this allows Cozy to quickly discover nonintuitive "
        + "solutions.")
enable_eviction = Option("eviction", bool, True)
cost_pruning = Option("prune-using-cost", bool, False,
    description="During synthesis, skip expressions that are more expensive "
        + "than the current best. This makes Cozy faster since it caches "
        + "fewer expressions, but also makes Cozy slower since it needs to do "
        + "more work when it sees each one for the first time.")

# Options that control `possibly_useful`
allow_conditional_state = Option("allow-conditional-state", bool, True,
    description="If enabled, Cozy is allowed to emit concretization functions "
        + "of the form `cond ? x : y`. Sometimes this is desireable, but it "
        + "can also lead to situations where the synthesized data structure "
        + "needs to do an enormous amount of work when `cond` changes value.")
allow_peels = Option("allow-peels", bool, False,
    description="If enabled, Cozy is allowed to emit concretization functions "
        + "that remove or \"peel\" a single element off of a set. This is "
        + "rarely useful and can lead to very slow data structures.")
allow_big_sets = Option("allow-big-sets", bool, False,
    description="If enabled, Cozy is allowed to store collections on the data "
        + "structure whose maximum size may exceed that of any collection in "
        + "the specification. Usually this is undesireable as it can produce "
        + "data structures that are fast but exhaust available memory.")
allow_big_maps = Option("allow-big-maps", bool, False,
    description="Similar to --allow-big-sets, but for hash maps.")
allow_int_arithmetic_state = Option("allow-int-arith-state", bool, True,
    description="If enabled, Cozy is allowed to do integer arithmetic in "
        + "concretization functions. In rare cases this can cause Cozy to "
        + "\"spin out\" and produce increasingly bizarre concretization "
        + "functions.")
allow_nonzero_state_constants = Option("allow-nonzero-state-constants", bool, True,
    description="If enabled, Cozy is allowed to use non-zero numerical "
        + "constants in concretization functions.  Note that disabling this "
        + "option only makes the task more difficult, as Cozy can still "
        + "discover ways to produce integer constants from other expressions.")
allow_binop_state = Option("allow-binop-state", bool, False,
    description="If enabled, Cozy is allowed to use fast constant-time binary "
        + "operators in concretization functions.  Generally it is more "
        + "desireable for Cozy to use simpler concretization functions and "
        + "have the data structure do fast binary operations at run time.")

improvement_limit = Option("improvement-limit", int, -1,
    description="Applies a limit to the number of improvements cozy will run"
        + "on the specification.  (-1) means no limit.")

allow_random_assignment_heuristic = Option("allow-random-assignment-heuristic", bool, True,
    description="Use a random assignment heuristic instead of solver to solve sat/unsat problem")

def never_stop():
    """Takes no arguments, always returns False."""
    return False

def improve(
        target        : Exp,
        context       : Context,
        assumptions   : Exp                = ETRUE,
        stop_callback : Callable[[], bool] = never_stop,
        hints         : [Exp]              = (),
        examples      : [{str:object}]     = (),
        cost_model    : CostModel          = None,
        ops           : [Op]               = (),
        improve_count : Value              = None):
    """Improve the target expression using enumerative synthesis.

    This function is a generator that yields increasingly better and better
    versions of the input expression `target` in the given `context`.  The
    `cost_model` defines "better".

    It periodically calls `stop_callback` and exits gracefully when
    `stop_callback` returns True.

    Other parameters:
        - assumptions: a precondition.  The yielded improvements will only be
          correct when the assumptions are true.
        - hints: expressions that might be useful.  These will be explored
          first when looking for improvements.
        - examples: inputs that will be used internally to differentiate
          semantically distinct expressions.  This procedure discovers more
          examples as it runs, so there usually isn't a reason to provide any.
        - ops: update operations.  This function may make different choices
          about what expressions are state expressions based on what changes
          can happen to that state.

    Key differences from "regular" enumerative synthesis:
        - Expressions are either "state" expressions or "runtime" expressions,
          allowing this algorithm to choose what things to store on the data
          structure and what things to compute at query execution time. (The
          cost model is ultimately responsible for this choice.)
        - If a better version of *any subexpression* for the target is found,
          it is immediately substituted in and the overall expression is
          returned. This "smooths out" the search space a little, allowing us
          find kinda-good solutions very quickly, even if the best possible
          solution is out of reach.  This is more desireable than running for
          an indeterminate amount of time doing nothing.
    """

    print("call to improve:")
    print("""improve(
        target={target!r},
        context={context!r},
        assumptions={assumptions!r},
        stop_callback={stop_callback!r},
        hints={hints!r},
        examples={examples!r},
        cost_model={cost_model!r},
        ops={ops!r})""".format(
            target=target,
            context=context,
            assumptions=assumptions,
            stop_callback=stop_callback,
            hints=hints,
            examples=examples,
            cost_model=cost_model,
            ops=ops))

    target = inline_lets(target)
    target = freshen_binders(target, context)
    assumptions = freshen_binders(assumptions, context)

    if heuristic_done(target):
        print("The target already looks great!")
        return

    print()
    print("improving: {}".format(pprint(target)))
    print("subject to: {}".format(pprint(assumptions)))
    print()

    is_wf = exp_wf(target, context=context, assumptions=assumptions)
    assert is_wf, "initial target is not well-formed: {}".format(is_wf)

    state_vars = [v for (v, p) in context.vars() if p == STATE_POOL]
    if eliminate_vars.value and can_elim_vars(target, assumptions, state_vars):
        print("This job does not depend on state_vars.")
        # TODO: what can we do about it?

    hints = ([freshen_binders(h, context) for h in hints]
        + [freshen_binders(wrap_naked_statevars(a, state_vars), context) for a in break_conj(assumptions)]
        + [target])
    print("{} hints".format(len(hints)))
    for h in hints:
        print(" - {}".format(pprint(h)))
    vars = list(v for (v, p) in context.vars())
    funcs = context.funcs()

    solver = solver_for_context(context, assumptions=assumptions)

    if not solver.satisfiable(ETRUE):
        print("assumptions are unsat; this query will never be called")
        yield construct_value(target.type)
        return

    is_good = possibly_useful(solver, target, context)
    assert is_good, "WARNING: this target is already a bad idea\n is_good = {}, target = {}".format(is_good, target)

    examples = list(examples)

    if cost_model is None:
        cost_model = CostModel(funcs=funcs, assumptions=assumptions)

    watched_targets = [target]
    blacklist = {}

    while True:

        # 0. check whether we are allowed to keep working
        if improve_count is not None:
            with improve_count.get_lock():
                if improvement_limit.value != -1 and improve_count.value >= improvement_limit.value:
                    print("improve limit reached")
                    return

                # NOTE: This code treats `improve_count` as a "budget", and it
                # "pays" for the improvement before actually doing the work.
                # Put another way, `improve_count.value` is the sum of (1) the
                # number of improvements found and (2) the number of
                # improvements being actively worked on.
                improve_count.value += 1

        # 1. find any potential improvement to any sub-exp of target
        for new_target in search_for_improvements(
                targets=watched_targets,
                wf_solver=solver,
                context=context,
                examples=examples,
                cost_model=cost_model,
                stop_callback=stop_callback,
                hints=hints,
                ops=ops,
                blacklist=blacklist):
            print("Found candidate improvement: {}".format(pprint(new_target)))

            # 2. check
            with task("verifying candidate"):
                # try heuristic based solving first
                e = ENot(EEq(target, new_target))
                if allow_random_assignment_heuristic.value:
                    if random_assignment.unsatisfiable(e):
                        counterexample = None
                    else:
                        try:
                            counterexample = random_assignment.satisfy(e, solver, assumptions)
                        except Exception:
                            counterexample = None
                        if counterexample is None:
                            event("failed assignmnents: for %s\n" % e)
                            counterexample = solver.satisfy(e)
                            event("counter-example: for %s\n" % counterexample)
                else:
                    counterexample = solver.satisfy(e)

            if counterexample is not None:
                if counterexample in examples:
                    print("assumptions = {!r}".format(assumptions))
                    print("duplicate example: {!r}".format(counterexample))
                    print("old target = {!r}".format(target))
                    print("new target = {!r}".format(new_target))
                    raise Exception("got a duplicate example")
                # a. if incorrect: add example, restart
                examples.append(counterexample)
                print("new example: {!r}".format(counterexample))
                print("wrong; restarting with {} examples".format(len(examples)))
                break
            else:
                # b. if correct: yield it, watch the new target, goto 1
                print("The candidate is valid!")
                print(repr(new_target))
                print("Determining whether to yield it...")
                with task("updating frontier"):
                    to_evict = []
                    keep = True
                    old_better = None
                    for old_target in watched_targets:
                        evc = retention_policy(new_target, context, old_target, context, RUNTIME_POOL, cost_model)
                        if old_target not in evc:
                            to_evict.append(old_target)
                        if new_target not in evc:
                            old_better = old_target
                            keep = False
                            break
                    for t in to_evict:
                        watched_targets.remove(t)
                    if not keep:
                        print("Whoops! Looks like we already found something better.")
                        print(" --> {}".format(pprint(old_better)))
                        continue
                    if target in to_evict:
                        print("Yep, it's an improvement!")
                        yield new_target
                        if heuristic_done(new_target):
                            print("target now matches doneness heuristic")
                            return
                        target = new_target
                    else:
                        print("Nope, it isn't substantially better!")

                watched_targets.append(new_target)
                print("Now watching {} targets".format(len(watched_targets)))
                break

SearchInfo = namedtuple("SearchInfo", (
    "context",
    "targets",
    "target_fingerprint",
    "examples",
    "check_wf",
    "cost_model",
    "blacklist"))

def search_for_improvements(
        targets       : [Exp],
        wf_solver     : ModelCachingSolver,
        context       : Context,
        examples      : [{str:object}],
        cost_model    : CostModel,
        stop_callback : Callable[[], bool],
        hints         : [Exp],
        ops           : [Op],
        blacklist     : {(Exp, Context, Pool, Exp) : str}):
    """Search for potential improvements to any of the target expressions.

    This function yields expressions that look like improvements (or are
    ambiguous with respect to some target).  The expressions are only
    guaranteed to be correct on the given examples.

    This function may add new items to the given blacklist.
    """

    root_ctx = context
    def check_wf(e, ctx, pool):
        with task("pruning", size=e.size()):
            is_wf = exp_wf(e, pool=pool, context=ctx, solver=wf_solver)
            if not is_wf:
                return is_wf
            res = possibly_useful(wf_solver, e, ctx, pool, ops=ops)
            if not res:
                return res
            if cost_pruning.value and pool == RUNTIME_POOL and cost_model.compare(e, targets[0], ctx, pool) == Order.GT:
                return No("too expensive")
            return True

    with task("setting up hints"):
        frags = list(unique(itertools.chain(
            *[all_subexpressions_with_context_information(t, root_ctx) for t in targets],
            *[all_subexpressions_with_context_information(h, root_ctx) for h in hints])))
        frags.sort(key=hint_order)
        enum = Enumerator(
            examples=examples,
            cost_model=cost_model,
            check_wf=check_wf,
            hints=frags,
            heuristics=try_optimize,
            stop_callback=stop_callback,
            do_eviction=enable_eviction.value)

    target_fp = Fingerprint.of(targets[0], examples)

    with task("setting up watches"):
        watches_by_context = OrderedDict()
        for target in targets:
            for e, ctx, pool in unique(all_subexpressions_with_context_information(target, context=root_ctx, pool=RUNTIME_POOL)):
                l = watches_by_context.get(ctx)
                if l is None:
                    l = []
                    watches_by_context[ctx] = l
                l.append((target, e, pool))

        watches = OrderedDict()
        for ctx, exprs in watches_by_context.items():
            exs = ctx.instantiate_examples(examples)
            for target, e, pool in exprs:
                fp = Fingerprint.of(e, exs)
                k = (fp, ctx, pool)
                l = watches.get(k)
                if l is None:
                    l = []
                    watches[k] = l
                l.append((target, e))

        watched_ctxs = list(unique((ctx, pool) for _, _, ctx, pool in exploration_order(targets, root_ctx)))

    search_info = SearchInfo(
        context=root_ctx,
        targets=targets,
        target_fingerprint=target_fp,
        examples=examples,
        check_wf=check_wf,
        cost_model=cost_model,
        blacklist=blacklist)

    size = 0
    while True:

        print("starting minor iteration {} with |cache|={}".format(size, enum.cache_size()))
        if stop_callback():
            raise StopException()

        for ctx, pool in watched_ctxs:
            with task("searching for obvious substitutions", ctx=ctx, pool=pool_name(pool)):
                for info in enum.enumerate_with_info(size=size, context=ctx, pool=pool):
                    with task("searching for obvious substitution", expression=pprint(info.e)):
                        fp = info.fingerprint
                        for ((fpx, cc, pp), reses) in watches.items():
                            if cc != ctx or pp != pool:
                                continue

                            if not fpx.equal_to(fp):
                                continue

                            for target, watched_e in reses:
                                replacement = info.e
                                event("possible substitution: {} ---> {}".format(pprint(watched_e), pprint(replacement)))
                                event("replacement locations: {}".format(pprint(replace(target, root_ctx, RUNTIME_POOL, watched_e, ctx, pool, EVar("___")))))

                                if alpha_equivalent(watched_e, replacement):
                                    event("no change")
                                    continue

                                yield from _consider_replacement(target, watched_e, ctx, pool, replacement, search_info)

        if check_blind_substitutions.value:
            print("Guessing at substitutions...")
            for target, e, ctx, pool in exploration_order(targets, root_ctx):
                with task("checking substitutions",
                        target=pprint(replace(target, root_ctx, RUNTIME_POOL, e, ctx, pool, EVar("___"))),
                        e=pprint(e)):
                    for info in enum.enumerate_with_info(size=size, context=ctx, pool=pool):
                        with task("checking substitution", expression=pprint(info.e)):
                            if stop_callback():
                                raise StopException()
                            replacement = info.e
                            if replacement.type != e.type:
                                event("wrong type (is {}, need {})".format(pprint(replacement.type), pprint(e.type)))
                                continue
                            if alpha_equivalent(replacement, e):
                                event("no change")
                                continue
                            should_consider = should_consider_replacement(
                                target, root_ctx,
                                e, ctx, pool, Fingerprint.of(e, ctx.instantiate_examples(examples)),
                                info.e, info.fingerprint)
                            if not should_consider:
                                event("skipped; `should_consider_replacement` returned {}".format(should_consider))
                                continue

                            yield from _consider_replacement(target, e, ctx, pool, replacement, search_info)

        if not enum.expressions_may_exist_above_size(context, RUNTIME_POOL, size):
            raise StopException("no more expressions can exist above size={}".format(size))

        size += 1

def _consider_replacement(
        target      : Exp,
        e           : Exp,
        ctx         : Context,
        pool        : Pool,
        replacement : Exp,
        info        : SearchInfo):
    """Helper for search_for_improvements.

    This procedure decides whether replacing `e` with `replacement` in the
    given `target` is an improvement.  If yes, it yields the result of the
    replacement.  Otherwise it yields nothing.

    Parameters:
     - target: the top-level expression to improve
     - e: a subexpression of the target
     - ctx: e's context in the target
     - pool: e's pool in the target
     - replacement: a possible replacement for e
     - info: a SearchInfo object with auxiliary data

    This procedure may add items to info.blacklist.
    """
    context = info.context
    blacklist = info.blacklist
    k = (e, ctx, pool, replacement)
    if enable_blacklist.value and k in blacklist:
        event("blacklisted")
        print("skipping blacklisted substitution: {} ---> {} ({})".format(pprint(e), pprint(replacement), blacklist[k]))
        return
    new_target = freshen_binders(replace(
        target, context, RUNTIME_POOL,
        e, ctx, pool,
        replacement), context)
    if any(alpha_equivalent(t, new_target) for t in info.targets):
        event("already seen")
        return
    wf = info.check_wf(new_target, context, RUNTIME_POOL)
    if not wf:
        msg = "not well-formed [wf={}]".format(wf)
        event(msg)
        blacklist[k] = msg
        return
    if not Fingerprint.of(new_target, info.examples).equal_to(info.target_fingerprint):
        msg = "not correct"
        event(msg)
        blacklist[k] = msg
        return
    if not info.cost_model.compare(new_target, target, context, RUNTIME_POOL).could_be(Order.LT):
        msg = "not an improvement"
        event(msg)
        blacklist[k] = msg
        return
    print("FOUND A GUESS")
    print(" * in {}".format(pprint(target), pprint(e), pprint(replacement)))
    print(" * replacing {}".format(pprint(e)))
    print(" * with {}".format(pprint(replacement)))
    from cozy.structures.treemultiset import ETreeMultisetElems
    if isinstance(e, ETreeMultisetElems) and isinstance(e.e, EStateVar) and \
            isinstance(replacement, EStateVar) and isinstance(replacement.e, ETreeMultisetElems):
        # FIXME(zhen): current enumerator will always try to make ETreeMultisetElems a state var
        # FIXME(zhen): we don't want this because we need to put TreeSet into state var, rather than its iterator
        # FIXME(zhen): I still don't know how to fix this in a sensible way, but giving up an "improvement"
        # FIXME(zhen): should be okay temporarily
        print("give up {} -> {}".format(pprint(e), pprint(replacement)))
        return
    yield new_target

def can_elim_vars(spec : Exp, assumptions : Exp, vs : [EVar]):
    """Does any execution of `spec` actually depend on any of `vs`?

    It is possible for a variable to appear in an expression like `spec`
    without affecting its value.  This function uses the solver to
    determine whether any of the given variables can affect the output of
    `spec`.
    """
    spec = strip_EStateVar(spec)
    sub = { v.id : fresh_var(v.type) for v in vs }
    return valid(EImplies(
        EAll([assumptions, subst(assumptions, sub)]),
        EEq(spec, subst(spec, sub))))

_DONE = set([EVar, EEnumEntry, ENum, EStr, EBool, EEmptyList, ENull])
def heuristic_done(e : Exp):
    """Returns True if it looks like `e` is as good as it can be ("done").

    This does not guarantee that `e` is optimal with respect to the cost model,
    but there are some cases where `e` is good enough and we'd rather not waste
    resources looking harder.
    """

    # Currently, these cases are considered "done":
    #  * variables
    #  * literals
    #  * a singleton set of a done expression
    #  * a field lookup on a done expression
    #  * a constant-time unary operator on a done expression
    return (
        (type(e) in _DONE) or
        (isinstance(e, ESingleton) and heuristic_done(e.e)) or
        (isinstance(e, EStateVar) and heuristic_done(e.e)) or
        (isinstance(e, EGetField) and heuristic_done(e.e)) or
        (isinstance(e, EUnaryOp) and e.op not in LINEAR_TIME_UOPS and heuristic_done(e.e)))

def exploration_order(targets : [Exp], context : Context, pool : Pool = RUNTIME_POOL):
    """
    What order should subexpressions of the given targets be explored for
    possible improvements?

    Yields (target, subexpression, subcontext, subpool) tuples.
    """

    # current policy (earlier requirements have priority):
    #  - visit runtime expressions first
    #  - visit low-complexity contexts first
    #  - visit small expressions first
    def sort_key(tup):
        e, ctx, p = tup
        return (0 if p == RUNTIME_POOL else 1, ctx.complexity(), e.size())

    for target in targets:
        for e, ctx, p in sorted(unique(all_subexpressions_with_context_information(target, context, pool=pool)), key=sort_key):
            yield (target, e, ctx, p)

def should_consider_replacement(
        target         : Exp,
        target_context : Context,
        subexp         : Exp,
        subexp_context : Context,
        subexp_pool    : Pool,
        subexp_fp      : Fingerprint,
        replacement    : Exp,
        replacement_fp : Fingerprint) -> bool:
    """Heuristic that controls "blind" replacements.

    Besides replacing subexpressions with improved versions, Cozy also attempts
    "blind" replacements where the subexpression and the replacement do not
    behave exactly the same.  In some cases this can actually make a huge
    difference, for instance by replacing a collection with a singleton.

    However, not all blind replacements are worth trying.  This function
    controls which ones Cozy actually attempts.

    Preconditions:
     - subexp and replacement are both legal in (subexp_context, subexp_pool)
     - subexp and replacement have the same type
    """

    if not is_collection(subexp.type):
        return No("only collections matter")

    if not replacement_fp.subset_of(subexp_fp):
        return No("not a subset")

    return True

def hint_order(tup):
    """What order should the enumerator see hints?

    Takes an (e, ctx, pool) tuple as input and returns a sort key.
    """

    # current policy: visit smaller expressions first
    e, ctx, pool = tup
    return e.size()

def possibly_useful_nonrecursive(solver, e : Exp, context : Context, pool = RUNTIME_POOL, assumptions : Exp = ETRUE, ops : [Op] = ()) -> bool:
    """Heuristic filter to ignore expressions that are almost certainly useless."""

    state_vars  = OrderedSet(v for v, p in context.vars() if p == STATE_POOL)
    args        = OrderedSet(v for v, p in context.vars() if p == RUNTIME_POOL)
    assumptions = EAll([assumptions, context.path_condition()])
    at_runtime  = pool == RUNTIME_POOL

    h = extension_handler(type(e))
    if h is not None:
        res = h.possibly_useful(e, context, pool, assumptions, ops, solver)
        if not res:
            return res

    if isinstance(e, EStateVar) and not free_vars(e.e):
        return No("constant value in state position")
    if (isinstance(e, EDropFront) or isinstance(e, EDropBack)) and not at_runtime:
        return No("EDrop* in state position")
    if not allow_big_sets.value and isinstance(e, EFlatMap) and not at_runtime:
        return No("EFlatMap in state position")
    if not allow_int_arithmetic_state.value and not at_runtime and isinstance(e, EBinOp) and e.type == INT:
        return No("integer arithmetic in state position")
    if is_collection(e.type) and not is_scalar(e.type.elem_type):
        return No("collection of nonscalar: e {}\n elem_type: {}\n".format(e, e.type.elem_type))
    if isinstance(e.type, TMap) and not is_scalar(e.type.k):
        return No("bad key type {}".format(pprint(e.type.k)))
    if isinstance(e.type, TMap) and isinstance(e.type.v, TMap):
        return No("map to map")
    # This check is probably a bad idea: whether `the` is legal may depend on
    # the contex that the expression is embedded within, so we can't skip it
    # during synthesis just because it looks invalid now.
    # if isinstance(e, EUnaryOp) and e.op == UOp.The:
    #     len = EUnaryOp(UOp.Length, e.e).with_type(INT)
    #     if not valid(EImplies(assumptions, EBinOp(len, "<=", ENum(1).with_type(INT)).with_type(BOOL))):
    #         return No("illegal application of 'the': could have >1 elems")
    if not at_runtime and isinstance(e, EBinOp) and e.op == "-" and is_collection(e.type):
        return No("collection subtraction in state position")
    # if not at_runtime and isinstance(e, ESingleton):
    #     return No("singleton in state position")
    if not allow_nonzero_state_constants.value and not at_runtime and isinstance(e, ENum) and e.val != 0:
        return No("nonzero integer constant in state position")
    if not allow_binop_state.value and at_runtime and isinstance(e, EStateVar) and isinstance(e.e, EBinOp) and is_scalar(e.e.e1.type) and is_scalar(e.e.e2.type):
        return No("constant-time binary operator {!r} in state position".format(e.e.op))
    if not allow_conditional_state.value and not at_runtime and isinstance(e, ECond):
        return No("conditional in state position")
    if isinstance(e, EMakeMap2) and isinstance(e.e, EEmptyList):
        return No("trivially empty map")
    if isinstance(e, EMakeMap2) and isinstance(e.e, ESingleton):
        return No("really tiny map")
    if not at_runtime and (isinstance(e, EArgMin) or isinstance(e, EArgMax)):
        # Cozy has no way to efficiently implement mins/maxes when more than
        # one element may leave the collection.
        from cozy.state_maintenance import mutate
        for op in ops:
            elems = e.e
            elems_prime = mutate(elems, op.body)
            formula = EAll([assumptions] + list(op.assumptions) + [EGt(ELen(EBinOp(elems, "-", elems_prime).with_type(elems.type)), ONE)])
            if solver.satisfiable(formula):
                return No("more than one element might be removed during {}".format(op.name))
    if not allow_peels.value and not at_runtime and isinstance(e, EFilter):
        # catch "peels": removal of zero or one elements
        if solver.valid(EImplies(assumptions, ELe(ELen(EFilter(e.e, ELambda(e.predicate.arg, ENot(e.predicate.body))).with_type(e.type)), ONE))):
            return No("filter is a peel")
    if not allow_big_maps.value and not at_runtime and isinstance(e, EMakeMap2) and is_collection(e.type.v):
        all_collections = [sv for sv in state_vars if is_collection(sv.type)]
        total_size = ENum(0).with_type(INT)
        for c in all_collections:
            total_size = EBinOp(total_size, "+", EUnaryOp(UOp.Length, c).with_type(INT)).with_type(INT)
        my_size = EUnaryOp(UOp.Length, EFlatMap(EUnaryOp(UOp.Distinct, e.e).with_type(e.e.type), e.value_function).with_type(e.type.v)).with_type(INT)
        s = EImplies(
            assumptions,
            EBinOp(total_size, ">=", my_size).with_type(BOOL))
        if not solver.valid(s):
            return No("non-polynomial-sized map")

    return True

def possibly_useful(solver, e : Exp, context : Context, pool = RUNTIME_POOL, assumptions : Exp = ETRUE, ops : [Op] = ()) -> bool:
    """Ensure that every subexpression of `e` passes the `possibly_useful_nonrecursive` check."""
    for (sub, sub_ctx, sub_pool) in all_subexpressions_with_context_information(e, context, pool):
        res = possibly_useful_nonrecursive(solver, sub, sub_ctx, sub_pool, assumptions=assumptions, ops=ops)
        if not res:
            return res
    return True
