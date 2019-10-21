"""High-level synthesis routine for whole implementations.

This module exports one important function:
 - improve_implementation
"""

from collections import OrderedDict
import datetime
import itertools
from typing import Callable, Any
import sys
import os
import pickle
from queue import Empty
from multiprocessing import Value

from cozy.common import typechecked, OrderedSet, LINE_BUFFER_MODE
from cozy.syntax import Query, Op, Exp, EVar, EAll
from cozy.target_syntax import EStateVar
from cozy.syntax_tools import pprint, unpack_representation, shallow_copy, wrap_naked_statevars
from cozy.timeouts import Timeout
from cozy import jobs
from cozy.contexts import Context
from cozy.opts import Option
from cozy.cost_model import CostModel

from . import core
from .impls import Implementation

nice_children = Option("nice-children", bool, False,
    description='Apply a high Unix "niceness" value to child processes. '
        + "Cozy can spawn a lot of child processes during synthesis, so this "
        + "option exists to help control resource usage.")

log_dir = Option("log-dir", str, "/tmp",
    description="Location to place log files for child processes.")

class ImproveQueryJob(jobs.Job):
    @typechecked
    def __init__(self,
            state       : [EVar],
            assumptions : [Exp],
            q           : Query,
            context     : Context,
            k,
            hints       : [Exp]     = [],
            freebies    : [Exp]     = [],
            ops         : [Op]      = [],
            improve_count             = None):
        super().__init__()
        self.state = state
        self.assumptions = assumptions
        q = shallow_copy(q)
        q.ret = wrap_naked_statevars(q.ret, OrderedSet(state))
        self.q = q
        self.context = context
        self.hints = hints
        self.freebies = freebies
        self.ops = ops
        self.k = k
        self.improve_count = improve_count
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

            cost_model = CostModel(
                    funcs=self.context.funcs(),
                    assumptions=EAll(self.assumptions),
                    freebies=self.freebies,
                    ops=self.ops)

            try:
                for expr in itertools.chain((self.q.ret,), core.improve(
                        target=self.q.ret,
                        assumptions=EAll(self.assumptions),
                        context=self.context,
                        hints=self.hints,
                        stop_callback=lambda: self.stop_requested,
                        cost_model=cost_model,
                        ops=self.ops,
                        improve_count=self.improve_count)):

                    new_rep, new_ret = unpack_representation(expr)
                    self.k(new_rep, new_ret)
                print("PROVED OPTIMALITY FOR {}".format(self.q.name))
            except core.StopException:
                print("stopping synthesis of {}".format(self.q.name))
                return

def improve_implementation(
        impl              : Implementation,
        timeout           : datetime.timedelta = datetime.timedelta(seconds=60),
        progress_callback : Callable[[Implementation], Any] = None,
        improve_count     : Value = None,
        save              : str = None) -> Implementation:
    """Improve an implementation.

    This function tries to synthesize a better version of the given
    implementation. It returns the best version found within the given timeout.

    If provided, progress_callback will be called whenever a better
    implementation is found.  It will be given the better implementation, which
    it should not modify or cache.
    """

    start_time = datetime.datetime.now()

    # we statefully modify `impl`, so let's make a defensive copy which we will modify instead
    impl = impl.safe_copy()

    # worker threads ("jobs"), one per query
    improvement_jobs = []

    with jobs.SafeQueue() as solutions_q:

        def stop_jobs(js):
            """Stop the given jobs and remove them from `improvement_jobs`."""
            js = list(js)
            jobs.stop_jobs(js)
            for j in js:
                improvement_jobs.remove(j)

        def reconcile_jobs():
            """Sync up the current set of jobs and the set of queries.

            This function spawns new jobs for new queries and cleans up old
            jobs whose queries have been dead-code-eliminated."""

            # figure out what new jobs we need
            job_query_names  = set(j.q.name for j in improvement_jobs)
            new = []
            for q in impl.query_specs:
                if q.name not in job_query_names:
                    states_maintained_by_q = impl.states_maintained_by(q)
                    new.append(ImproveQueryJob(
                        impl.abstract_state,
                        list(impl.spec.assumptions) + list(q.assumptions),
                        q,
                        context=impl.context_for_method(q),
                        k=(lambda q: lambda new_rep, new_ret: solutions_q.put((q, new_rep, new_ret)))(q),
                        hints=[EStateVar(c).with_type(c.type) for c in impl.concretization_functions.values()],
                        freebies=[e for (v, e) in impl.concretization_functions.items() if EVar(v) in states_maintained_by_q],
                        ops=impl.op_specs,
                        improve_count=improve_count))

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
                # The guard on the next line might be false!
                # It might so happen that:
                #   - a job found a better version for q
                #   - a different job found a better version of some other query X
                #   - both improvements were in the `results` list pulled from the queue
                #   - we visited the improvement for X first
                #   - after cleanup, q is no longer needed and was removed
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
                        progress_callback(impl)
                    reconcile_jobs()
                else:
                    print("  (skipped; {} was aleady cleaned up)".format(q.name))

        if save:
            with open(save, "wb") as f:
                pickle.dump(impl, f)
                print("Saved implementation to file {}".format(save))

        # stop jobs
        print("Stopping jobs")
        stop_jobs(list(improvement_jobs))
        return impl
