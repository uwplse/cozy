from collections import namedtuple, deque, defaultdict
import datetime
import itertools
import sys

from cozy.common import typechecked, fresh_name, pick_to_sum, nested_dict
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

@typechecked
def pick_rep(q_ret : Exp, state : [EVar]) -> ([(EVar, Exp)], Exp):
    cm = CompositeCostModel(state)
    return min(infer_rep(state, q_ret), key=lambda r: cm.split_cost(*r), default=None)

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
        with open("/tmp/{}.log".format(self.q.name), "w") as f:
            sys.stdout = f
            print("STARTING IMPROVEMENT JOB {} (|examples|={})".format(self.q.name, len(self.examples or ())))

            all_types = self.ctx.all_types
            binders = []
            n_binders = 1 # TODO?
            for t in all_types:
                if isinstance(t, TBag):
                    binders += [fresh_var(t.t) for i in range(n_binders)]
                    for i in range(n_binders):
                        b = fresh_var(t)
                        binders.append(b)

            b = BinderBuilder(binders, self.state)
            if accelerate.value:
                b = AcceleratedBuilder(b, binders, self.state)

            try:
                for expr in itertools.chain((self.q.ret,), core.improve(
                        target=self.q.ret,
                        assumptions=EAll(self.assumptions),
                        hints=self.hints,
                        examples=self.examples,
                        binders=binders,
                        cost_model=CompositeCostModel(self.state + binders),
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
        q.args,
        q.assumptions if keep_assumptions else (),
        repl(q.ret))

@typechecked
def synthesize(
        spec      : Spec,
        per_query_timeout : datetime.timedelta = datetime.timedelta(seconds=60)) -> (Spec, dict):

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
    op_deltas = { op.name : inc.to_delta(spec.statevars, op) for op in spec.methods if isinstance(op, Op) }

    # op_stms[var][op_name] gives the statement necessary to update
    # `var` when `op_name` is called
    op_stms = nested_dict(2, lambda: SNoOp())

    # the actual worker threads
    improvement_jobs = []
    from queue import Empty
    with jobs.SafeQueue() as solutions_q:

        def push_goal(q : Query):
            specs.append(q)
            qargs = set(EVar(a).with_type(t) for (a, t) in q.args)
            rep = [(fresh_var(v.type), v) for v in free_vars(q) if v not in qargs]
            ret = subst(q.ret, { sv.id:v for (v, sv) in rep })
            set_impl(q, rep, ret)
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
                print("###### INCREMENTALIZING: {}".format(op.name))
                (member, delta) = op_deltas[op.name]
                # print(member, delta)
                for new_member, projection in rep:
                    (state_update, subqueries) = inc.derivative(projection, member, delta, state_vars, list(op.assumptions))
                    # print(state_update, subqueries)
                    state_update_stm = inc.apply_delta_in_place(new_member, state_update)
                    # print(pprint(state_update_stm))
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
                            print("########### NEW SUBGOAL: {}".format(pprint(sub_q)))
                            push_goal(sub_q)
                    op_stms[new_member][op.name] = state_update_stm

        # set initial implementations
        for q in spec.methods:
            if isinstance(q, Query):
                push_goal(q)

        # wait for results
        timeout = Timeout(per_query_timeout)
        while any(not j.done for j in improvement_jobs) and not timeout.is_timed_out():
            try:
                (q, new_rep, new_ret) = solutions_q.get(timeout=0.5)
                if q.name in [qq.name for qq in specs]:
                    print("SOLUTION FOR {}".format(q.name))
                    print("-" * 40)
                    for (sv, proj) in new_rep:
                        print("  {} : {} = {}".format(sv.id, pprint(sv.type), pprint(proj)))
                    print("  return {}".format(pprint(new_ret)))
                    print("-" * 40)
                    # this might fail if a better solution was enqueued but the job has
                    # already been stopped and cleaned up
                    set_impl(q, new_rep, new_ret)
                    cleanup()
            except Empty:
                pass

        # stop jobs
        print("Stopping jobs")
        stop_jobs(list(improvement_jobs))

        # construct new queries
        new_queries = list(impls.values())

        # construct new op implementations
        new_ops = []
        for op in ops:
            stms = [ ss[op.name] for ss in op_stms.values() ]
            if isinstance(op_deltas[op.name][1], inc.BagElemUpdated):
                stms.append(op.body)
            new_stms = seq(stms)
            new_ops.append(Op(
                op.name,
                op.args,
                [],
                new_stms))

        # assemble final result
        state_var_exps = { }
        for (v, e) in new_state_vars:
            state_var_exps[v.id] = e
            print("{} : {} = {}".format(v.id, pprint(v.type), pprint(e)))

        new_statevars = [(v, e.type) for (v, e) in state_var_exps.items()]
        return (Spec(
            spec.name,
            spec.types,
            spec.extern_funcs,
            new_statevars,
            [],
            new_queries + new_ops), state_var_exps)
