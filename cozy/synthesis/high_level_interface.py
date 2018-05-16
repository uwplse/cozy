from collections import namedtuple, deque, defaultdict, OrderedDict
import datetime
import itertools
import sys
import os
from queue import Empty

from cozy.common import typechecked, fresh_name, pick_to_sum, nested_dict, find_one, OrderedSet
from cozy.target_syntax import *
import cozy.syntax_tools
from cozy.syntax_tools import all_types, alpha_equivalent, BottomUpExplorer, BottomUpRewriter, free_vars, pprint, subst, implies, fresh_var, mk_lambda, all_exps, equal, is_scalar, tease_apart, shallow_copy, wrap_naked_statevars
from cozy.timeouts import Timeout, TimeoutException
from cozy import jobs
from cozy.contexts import RootCtx
from cozy.solver import valid
from cozy.opts import Option

from . import core
from .impls import Implementation

nice_children = Option("nice-children", bool, False)
log_dir = Option("log-dir", str, "/tmp")
SynthCtx = namedtuple("SynthCtx", ["all_types", "basic_types"])
LINE_BUFFER_MODE = 1 # see help for open() function

class ImproveQueryJob(jobs.Job):
    @typechecked
    def __init__(self,
            ctx : SynthCtx,
            state : [EVar],
            assumptions : [Exp],
            q : Query,
            k,
            hints : [Exp] = [],
            funcs : { str:TFunc } = { }):
        assert all(v in state for v in free_vars(q)), "Oops, query looks malformed due to {}:\n{}\nfree_vars({})".format([v for v in free_vars(q) if v not in state], pprint(q), repr(q))
        super().__init__()
        self.ctx = ctx
        self.state = state
        self.assumptions = assumptions
        q = shallow_copy(q)
        q.ret = wrap_naked_statevars(q.ret, OrderedSet(state))
        self.q = q
        self.hints = hints
        self.k = k
        self.funcs = OrderedDict(funcs)
    def __str__(self):
        return "ImproveQueryJob[{}]".format(self.q.name)
    def run(self):
        print("STARTING IMPROVEMENT JOB {}".format(self.q.name))
        os.makedirs(log_dir.value, exist_ok=True)
        with open(os.path.join(log_dir.value, "{}.log".format(self.q.name)), "w", buffering=LINE_BUFFER_MODE) as f:
            sys.stdout = f
            print("STARTING IMPROVEMENT JOB {}".format(self.q.name))
            print(pprint(self.q))

            if nice_children.value:
                os.nice(20)

            ctx = RootCtx(
                state_vars=self.state,
                args=[EVar(v).with_type(t) for (v, t) in self.q.args],
                funcs=self.funcs)

            try:
                for expr in itertools.chain((self.q.ret,), core.improve(
                        target=self.q.ret,
                        assumptions=EAll(self.assumptions),
                        context=ctx,
                        hints=self.hints,
                        stop_callback=lambda: self.stop_requested)):

                    new_rep, new_ret = tease_apart(expr)
                    self.k(new_rep, new_ret)
                print("PROVED OPTIMALITY FOR {}".format(self.q.name))
            except core.StopException:
                print("stopping synthesis of {}".format(self.q.name))
                return

@typechecked
def improve_implementation(
        impl              : Implementation,
        timeout           : datetime.timedelta = datetime.timedelta(seconds=60),
        progress_callback = None) -> Implementation:

    start_time = datetime.datetime.now()

    # we statefully modify `impl`, so let's make a defensive copy
    impl = Implementation(
        impl.spec,
        list(impl.concrete_state),
        list(impl.query_specs),
        OrderedDict(impl.query_impls),
        defaultdict(SNoOp, impl.updates),
        defaultdict(SNoOp, impl.handle_updates))

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
                        k=(lambda q: lambda new_rep, new_ret: solutions_q.put((q, new_rep, new_ret)))(q),
                        hints=[EStateVar(c).with_type(c.type) for c in impl.concretization_functions.values()],
                        funcs=impl.extern_funcs))

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
        timeout = Timeout(timeout)
        done = False
        while not done and not timeout.is_timed_out():
            for j in improvement_jobs:
                if j.done:
                    if j.successful:
                        j.join()
                    else:
                        print("failed job: {}".format(j), file=sys.stderr)
                        # raise Exception("failed job: {}".format(j))

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

            improvements = list(improved_queries_by_name.values())
            def index_of(l, p):
                if not isinstance(l, list):
                    l = list(l)
                for i in range(len(l)):
                    if p(l[i]):
                        return i
                return -1
            improvements.sort(key = lambda i: index_of(impl.query_specs, lambda qq: qq.name == i[0].name))
            print("update order:")
            for (q, _, _) in improvements:
                print("  --> {}".format(q.name))

            # update query implementations
            i = 1
            for (q, new_rep, new_ret) in improvements:
                if timeout.is_timed_out():
                    break

                print("considering update {}/{}...".format(i, len(improvements)))
                i += 1
                # this guard might be false if a better solution was
                # enqueued but the job has already been cleaned up
                if q.name in [qq.name for qq in impl.query_specs]:
                    elapsed = datetime.datetime.now() - start_time
                    print("SOLUTION FOR {} AT {} [size={}]".format(q.name, elapsed, new_ret.size() + sum(proj.size() for (v, proj) in new_rep)))
                    print("-" * 40)
                    for (sv, proj) in new_rep:
                        print("  {} : {} = {}".format(sv.id, pprint(sv.type), pprint(proj)))
                    print("  return {}".format(pprint(new_ret)))
                    print("-" * 40)
                    impl.set_impl(q, new_rep, new_ret)

                    # clean up
                    impl.cleanup()
                    if progress_callback is not None:
                        progress_callback((impl, impl.code, impl.concretization_functions))
                    reconcile_jobs()
                else:
                    print("  (skipped)")

        # stop jobs
        print("Stopping jobs")
        stop_jobs(list(improvement_jobs))
        return impl
