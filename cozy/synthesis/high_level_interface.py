from collections import namedtuple, deque, defaultdict, OrderedDict
import datetime
import itertools
import sys
from queue import Empty

from cozy.common import typechecked, fresh_name, pick_to_sum, nested_dict, find_one
from cozy.target_syntax import *
import cozy.syntax_tools
from cozy.syntax_tools import all_types, alpha_equivalent, BottomUpExplorer, BottomUpRewriter, free_vars, pprint, subst, implies, fresh_var, mk_lambda, all_exps, equal, is_scalar
import cozy.incrementalization as inc
from cozy.timeouts import Timeout, TimeoutException
from cozy.cost_model import CompositeCostModel
from cozy.rep_inference import infer_rep
from cozy import jobs
from cozy.solver import valid
from cozy.opts import Option

from . import core
from .impls import Implementation
from .grammar import BinderBuilder
from .acceleration import AcceleratedBuilder
from .misc import rewrite_ret, queries_equivalent

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
                    core.fixup_binders(expr, binders, throw=True)
                    done = True
                except:
                    pass
                n_binders += 1

            binders = [fresh_var(t) for t in all_types if is_scalar(t) for i in range(n_binders)]
            print("Using {} binders".format(n_binders))
            relevant_state_vars = [v for v in self.state if v in free_vars(EAll(self.assumptions)) | free_vars(self.q.ret)]
            used_vars = free_vars(self.q.ret)
            for a in self.q.assumptions:
                used_vars |= free_vars(a)
            args = [EVar(v).with_type(t) for (v, t) in self.q.args]
            args = [a for a in args if a in used_vars]
            b = BinderBuilder(binders, relevant_state_vars, args)
            if accelerate.value:
                b = AcceleratedBuilder(b, binders, relevant_state_vars, args)

            try:
                for expr in itertools.chain((self.q.ret,), core.improve(
                        target=self.q.ret,
                        assumptions=EAll(self.assumptions),
                        hints=self.hints,
                        examples=self.examples,
                        binders=binders,
                        state_vars=relevant_state_vars,
                        args=args,
                        cost_model=CompositeCostModel(),
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

@typechecked
def improve_implementation(
        impl              : Implementation,
        per_query_timeout : datetime.timedelta = datetime.timedelta(seconds=60),
        progress_callback = None) -> Implementation:

    # we statefully modify `impl`, so let's make a defensive copy
    impl = Implementation(
        impl.spec,
        list(impl.concrete_state),
        list(impl.query_specs),
        OrderedDict(impl.query_impls),
        defaultdict(SNoOp, impl.updates))

    # gather root types
    types = list(all_types(impl.spec))
    basic_types = set(t for t in types if is_scalar(t))
    basic_types |= { BOOL, INT }
    print("basic types:")
    for t in basic_types:
        print("  --> {}".format(pprint(t)))
    basic_types = list(basic_types)
    ctx = SynthCtx(all_types=types, basic_types=basic_types)

    # the actual worker threads
    improvement_jobs = []

    with jobs.SafeQueue() as solutions_q:

        def stop_jobs(js):
            js = list(js)
            jobs.stop_jobs(js)
            for j in js:
                improvement_jobs.remove(j)

        def reconcile_jobs():
            # figure out what new jobs we need
            job_query_names  = set(j.q.name for j in improvement_jobs)
            new = []
            for q in impl.query_specs:
                if q.name not in job_query_names:
                    new.append(ImproveQueryJob(
                        ctx,
                        impl.abstract_state,
                        list(impl.spec.assumptions) + list(q.assumptions),
                        q,
                        k=(lambda q: lambda new_rep, new_ret: solutions_q.put((q, new_rep, new_ret)))(q)))

            # figure out what old jobs we can stop
            impl_query_names = set(q.name for q in impl.query_specs)
            old = [j for j in improvement_jobs if j.q.name not in impl_query_names]

            # make it so
            stop_jobs(old)
            for j in new:
                j.start()
            improvement_jobs.extend(new)

        # start jobs
        reconcile_jobs()

        # wait for results
        timeout = Timeout(per_query_timeout)
        done = False
        while not done and not timeout.is_timed_out():
            for j in improvement_jobs:
                if j.done:
                    if j.successful:
                        j.join()
                    else:
                        raise Exception("failed job: {}".format(j))

            done = all(j.done for j in improvement_jobs)

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
            i = 1
            for (q, new_rep, new_ret) in improved_queries_by_name.values():
                print("considering update {}/{}...".format(i, len(improved_queries_by_name)))
                i += 1
                # this guard might be false if a better solution was
                # enqueued but the job has already been cleaned up
                if q.name in [qq.name for qq in impl.query_specs]:
                    print("SOLUTION FOR {} [size={}]".format(q.name, new_ret.size() + sum(proj.size() for (v, proj) in new_rep)))
                    print("-" * 40)
                    for (sv, proj) in new_rep:
                        print("  {} : {} = {}".format(sv.id, pprint(sv.type), pprint(proj)))
                    print("  return {}".format(pprint(new_ret)))
                    print("-" * 40)
                    impl.set_impl(q, new_rep, new_ret)

            # clean up
            impl.cleanup()
            if progress_callback is not None:
                progress_callback((impl.code, impl.concretization_functions))
            reconcile_jobs()

        # stop jobs
        print("Stopping jobs")
        stop_jobs(list(improvement_jobs))
        return impl
