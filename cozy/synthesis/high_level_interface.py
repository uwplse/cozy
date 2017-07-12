from collections import namedtuple, deque, defaultdict, OrderedDict
import datetime
import itertools
import sys

from cozy.common import typechecked, fresh_name, pick_to_sum, nested_dict, find_one
from cozy.target_syntax import *
import cozy.syntax_tools
from cozy.syntax_tools import all_types, alpha_equivalent, BottomUpExplorer, BottomUpRewriter, free_vars, pprint, subst, implies, fresh_var, mk_lambda, all_exps, equal, is_scalar
import cozy.incrementalization as inc
from cozy.typecheck import INT, BOOL
from cozy.timeouts import Timeout, TimeoutException
from cozy.cost_model import CompositeCostModel
from cozy.rep_inference import infer_rep
from cozy import jobs
from cozy.solver import valid
from cozy.opts import Option

from . import core
from .grammar import BinderBuilder
from .acceleration import AcceleratedBuilder

accelerate = Option("acceleration-rules", bool, True)
SynthCtx = namedtuple("SynthCtx", ["all_types", "basic_types"])
LINE_BUFFER_MODE = 1 # see help for open() function

@typechecked
def pick_rep(q_ret : Exp, state : [EVar]) -> ([(EVar, Exp)], Exp):
    return find_one(infer_rep(state, q_ret))

class ImproveQueryJob(jobs.Job):
    def __init__(self,
            ctx : SynthCtx,
            state : [EVar],
            assumptions : [Exp],
            q : Query,
            k,
            hints : [Exp] = [],
            examples : [dict] = None):
        super().__init__()
        self.ctx = ctx
        self.state = state
        self.assumptions = assumptions
        self.q = q
        assert all(v in state for v in free_vars(q)), str([v for v in free_vars(q) if v not in state])
        self.hints = hints
        self.examples = examples
        self.k = k
    def __str__(self):
        return "ImproveQueryJob[{}]".format(self.q.name)
    def run(self):
        print("STARTING IMPROVEMENT JOB {} (|examples|={})".format(self.q.name, len(self.examples or ())))
        with open("/tmp/{}.log".format(self.q.name), "w", buffering=LINE_BUFFER_MODE) as f:
            sys.stdout = f
            print("STARTING IMPROVEMENT JOB {} (|examples|={})".format(self.q.name, len(self.examples or ())))
            print(pprint(self.q))

            all_types = self.ctx.all_types
            n_binders = 1
            done = False
            expr = ETuple((EAll(self.assumptions), self.q.ret)).with_type(TTuple((BOOL, self.q.ret.type)))
            while not done:
                binders = []
                for t in all_types:
                    # if isinstance(t, TBag):
                    #     binders += [fresh_var(t.t) for i in range(n_binders)]
                    for i in range(n_binders):
                        b = fresh_var(t)
                        binders.append(b)
                try:
                    core.fixup_binders(expr, binders)
                    done = True
                except:
                    pass
                n_binders += 1

            binders = [fresh_var(t) for t in all_types if is_scalar(t) for i in range(n_binders)]
            print("Using {} binders".format(n_binders))
            relevant_state_vars = [v for v in self.state if v in free_vars(EAll(self.assumptions)) | free_vars(self.q.ret)]
            b = BinderBuilder(binders, relevant_state_vars)
            if accelerate.value:
                used_vars = free_vars(self.q.ret)
                for a in self.q.assumptions:
                    used_vars |= free_vars(a)
                args = [EVar(v).with_type(t) for (v, t) in self.q.args]
                args = [a for a in args if a in used_vars]
                b = AcceleratedBuilder(b, binders, relevant_state_vars, args)

            try:
                for expr in itertools.chain((self.q.ret,), core.improve(
                        target=self.q.ret,
                        assumptions=EAll(self.assumptions),
                        hints=self.hints,
                        examples=self.examples,
                        binders=binders,
                        cost_model=CompositeCostModel(self.state), # TODO: + binders?
                        builder=b,
                        stop_callback=lambda: self.stop_requested)):

                    r = pick_rep(expr, self.state)
                    if r is not None:
                        new_rep, new_ret = r
                        self.k(new_rep, new_ret)
                print("PROVED OPTIMALITY FOR {}".format(self.q.name))
            except core.StopException:
                print("stopping synthesis of {}".format(self.q.name))
                return

def rewrite_ret(q : Query, repl, keep_assumptions=True) -> Query:
    return Query(
        q.name,
        q.visibility,
        q.args,
        q.assumptions if keep_assumptions else (),
        repl(q.ret))

@typechecked
def synthesize(
        spec              : Spec,
        per_query_timeout : datetime.timedelta = datetime.timedelta(seconds=60),
        progress_callback = None) -> (Spec, { str : Exp }):

    # gather root types
    types = list(all_types(spec))
    basic_types = set(t for t in types if is_scalar(t))
    basic_types |= { BOOL, INT }
    print("basic types:")
    for t in basic_types:
        print("  --> {}".format(pprint(t)))
    basic_types = list(basic_types)
    ctx = SynthCtx(all_types=types, basic_types=basic_types)

    # collect state variables
    state_vars = [EVar(name).with_type(t) for (name, t) in spec.statevars]

    # collect queries
    specs          = [] # query specifications in terms of state_vars
    impls          = {} # query implementations (by name) in terms of new_state_vars
    new_state_vars = [] # list of (var, exp) pairs
    root_queries   = [q.name for q in spec.methods if isinstance(q, Query)]

    # transform ops to delta objects
    ops = [op for op in spec.methods if isinstance(op, Op)]
    op_deltas = { op.name : inc.delta_form(spec.statevars, op) for op in spec.methods if isinstance(op, Op) }

    # op_stms[var][op_name] gives the statement necessary to update
    # `var` when `op_name` is called
    op_stms = nested_dict(2, lambda: SNoOp())

    # the actual worker threads
    improvement_jobs = []
    from queue import Empty
    with jobs.SafeQueue() as solutions_q:

        def push_goal(q : Query):
            print("########### NEW SUBGOAL: {}".format(pprint(q)))
            specs.append(q)
            fvs = free_vars(q)
            # initial rep
            qargs = set(EVar(a).with_type(t) for (a, t) in q.args)
            rep = [(fresh_var(v.type), v) for v in fvs if v not in qargs]
            ret = subst(q.ret, { sv.id:v for (v, sv) in rep })
            set_impl(q, rep, ret)
            # wrap state vars
            q = rewrite_ret(q, lambda e: subst(e, { v.id : EStateVar(v).with_type(v.type) for v in fvs if v not in qargs }))
            # create job
            j = ImproveQueryJob(
                ctx,
                state_vars,
                list(spec.assumptions) + list(q.assumptions),
                q,
                k=lambda new_rep, new_ret: solutions_q.put((q, new_rep, new_ret)))
            improvement_jobs.append(j)
            j.start()

        def queries_used_by(thing):
            qs = set()
            class V(BottomUpExplorer):
                def visit_ECall(self, e):
                    qs.add(e.func)
            V().visit(thing)
            return qs

        def stop_jobs(js):
            for j in list(js):
                j.request_stop()
            for j in js:
                while True:
                    j.join(timeout=30)
                    if j.done:
                        break
                    print("job '{}' failed to stop in 30 seconds; it is probably deadlocked".format(j), file=sys.stderr)
                if not j.successful:
                    raise Exception("failed job: {}".format(j))
                improvement_jobs.remove(j)

        def cleanup():
            nonlocal new_state_vars

            # sort of like mark-and-sweep
            queries_to_keep = set(root_queries)
            state_vars_to_keep = set()
            changed = True
            while changed:
                changed = False
                for qname in queries_to_keep:
                    if qname in impls:
                        for sv in free_vars(impls[qname]):
                            if sv not in state_vars_to_keep:
                                state_vars_to_keep.add(sv)
                                changed = True
                for sv in state_vars_to_keep:
                    for op_stm in op_stms[sv].values():
                        for qname in queries_used_by(op_stm):
                            if qname not in queries_to_keep:
                                queries_to_keep.add(qname)
                                changed = True

            # remove old specs
            for q in list(specs):
                if q.name not in queries_to_keep:
                    specs.remove(q)

            # remove old implementations
            for qname in list(impls.keys()):
                if qname not in queries_to_keep:
                    del impls[qname]

            # remove old state vars
            new_state_vars = [ v for v in new_state_vars if any(v[0] in free_vars(q) for q in impls.values()) ]

            # stop jobs for old queries
            jobs_to_stop = [ j for j in improvement_jobs if j.q.name not in queries_to_keep ]
            stop_jobs(jobs_to_stop)

            # remove old method implementations
            for v in list(op_stms.keys()):
                if v not in [var for (var, exp) in new_state_vars]:
                    del op_stms[v]

        def equivalent(q1 : Query, q2 : Query):
            if q1.ret.type != q2.ret.type:
                return False
            q1args = dict(q1.args)
            q2args = dict(q2.args)
            if q1args != q2args:
                return False
            return valid(equal(q1.ret, q2.ret))

        def set_impl(q : Query, rep : [(EVar, Exp)], ret : Exp):
            to_remove = set()
            for (v, e) in rep:
                aeq = [ vv for (vv, ee) in new_state_vars if alpha_equivalent(e, ee) ]
                if aeq:
                    ret = subst(ret, { v.id : aeq[0] })
                    to_remove.add(v)
            rep = [ x for x in rep if x[0] not in to_remove ]

            new_state_vars.extend(rep)
            impls[q.name] = rewrite_ret(q, lambda prev: ret, keep_assumptions=False)

            for op in ops:
                # print("###### INCREMENTALIZING: {}".format(op.name))
                delta = op_deltas[op.name]
                for new_member, projection in rep:
                    (state_update_stm, subqueries) = inc.sketch_update(new_member, projection, subst(projection, delta), state_vars, list(op.assumptions))
                    for sub_q in subqueries:
                        qq = [qq for qq in specs if equivalent(qq, sub_q)]
                        if qq:
                            assert len(qq) == 1
                            qq = qq[0]
                            print("########### subgoal {} is equivalent to {}".format(sub_q.name, qq.name))
                            arg_reorder = [[x[0] for x in sub_q.args].index(a) for (a, t) in qq.args]
                            class Repl(BottomUpRewriter):
                                def visit_ECall(self, e):
                                    args = tuple(self.visit(a) for a in e.args)
                                    if e.func == sub_q.name:
                                        args = tuple(args[idx] for idx in arg_reorder)
                                        return ECall(qq.name, args).with_type(e.type)
                                    else:
                                        return ECall(e.func, args).with_type(e.type)
                            state_update_stm = Repl().visit(state_update_stm)
                        else:
                            push_goal(sub_q)
                    op_stms[new_member][op.name] = state_update_stm

        def result():
            # construct new queries
            new_queries = list(impls.values())

            # construct new op implementations
            new_ops = []
            for op in ops:
                stms = [ ss[op.name] for ss in op_stms.values() ]

                # append changes to op. arguments
                # TODO: detect pointer aliasing between op arguments and state vars?
                arg_changes = inc.delta_form(op.args, op)
                for v, t in op.args:
                    v = EVar(v).with_type(t)
                    (stm, subqueries) = inc.sketch_update(v, v, subst(v, arg_changes), [], [])
                    if subqueries:
                        raise NotImplementedError("update to {} in {} is too complex".format(v.id, op.name))
                    stms.append(stm)

                # construct new op. implementation
                new_stms = seq(stms)
                new_ops.append(Op(
                    op.name,
                    op.args,
                    [],
                    new_stms))

            # assemble final result
            state_var_exps = OrderedDict()
            for (v, e) in new_state_vars:
                state_var_exps[v.id] = e

            new_statevars = [(v, e.type) for (v, e) in state_var_exps.items()]
            return (Spec(
                spec.name,
                spec.types,
                spec.extern_funcs,
                new_statevars,
                [],
                new_queries + new_ops), state_var_exps)

        # set initial implementations
        for q in spec.methods:
            if isinstance(q, Query):
                push_goal(q)

        # wait for results
        timeout = Timeout(per_query_timeout)
        while any(not j.done for j in improvement_jobs) and not timeout.is_timed_out():
            try:
                # list of (Query, new_rep, new_ret) objects
                results = solutions_q.drain(block=True, timeout=0.5)
            except Empty:
                continue

            # group by query name, favoring later (i.e. better) solutions
            print("updating with {} new solutions".format(len(results)))
            improved_queries_by_name = OrderedDict()
            killed = 0
            for r in results:
                q, new_rep, new_ret = r
                if q.name in improved_queries_by_name:
                    killed += 1
                improved_queries_by_name[q.name] = r
            if killed:
                print(" --> dropped {} worse solutions".format(killed))

            # update query implementations
            for (q, new_rep, new_ret) in improved_queries_by_name.values():
                # this guard might be false if a better solution was
                # enqueued but the job has already been cleaned up
                if q.name in [qq.name for qq in specs]:
                    print("SOLUTION FOR {}".format(q.name))
                    print("-" * 40)
                    for (sv, proj) in new_rep:
                        print("  {} : {} = {}".format(sv.id, pprint(sv.type), pprint(proj)))
                    print("  return {}".format(pprint(new_ret)))
                    print("-" * 40)
                    set_impl(q, new_rep, new_ret)

            # clean up
            cleanup()
            if progress_callback is not None:
                progress_callback(result())

        # stop jobs
        print("Stopping jobs")
        stop_jobs(list(improvement_jobs))
        return result()
