"""Helper class to implement interruptable tasks.

Important things defined here:
 - Job: an abstract superclass for implementing interruptable tasks
 - stop_jobs: a function to interrupt some Jobs and wait for them to stop
 - SafeQueue: a queue with fewer caveats than multiprocessing.Queue; useful for
   collecting results from many Jobs

Internally, this module uses the `multiprocessing` module to get efficient
parallelism.  Clients of this module shouldn't normally concern themselves with
the `multiprocessing` module, but its use introduces some caveats:
 - There is no shared memory between Jobs, so the only way to collect results
   is by using a SafeQueue or by using `multiprocessing.Value` or
   `multiprocessing.Array`.
 - The synchronization primitives (i.e. locks) in the `threading` module do not
   affect Jobs; you must use the synchronization primitives in the
   `multiprocessing` module.
"""

from multiprocessing import Process, Array, Queue
from queue import Queue as PlainQueue, Empty, Full
import threading

from cozy.common import partition
from cozy.opts import Option

do_profiling = Option("profile", bool, False, description="Profile Cozy itself")

class Job(object):
    """An interruptable job.

    Subclasses must implement `self.run()`.  The implementation of `run` should
    frequently check `self.stop_requested` and return when it becomes true.
    Optionally, subclasses should implement `self.__str__()` to return a nice
    name for the job.

    Clients should invoke `.start()` after construction to start the Job.  They
    must invoke `.join()` at some point to clean up the Job's resources.

    Sample usage:

        class PrintLoop(Job):
            def run(self):
                while True:
                    if self.stop_requested:
                        return
                    print("still running!")

        job = PrintLoop()
        job.start()
        sleep(10)
        job.request_stop()
        job.join()

        assert job.done
        print("success?", job.successful)

    While a job is running, clients can check `job.done` to see if the job has
    completed yet.

    If .run() throws an uncaught exception, it is printed to standard error.

    When a job completes, clients can check `job.successful` to see if the job
    returned normally or threw an uncaught exception.  There is currently no
    way to retrieve the thrown exception, if any.
    """

    def __init__(self):
        self._thread = Process(target=self._run, daemon=True)
        self._flags = Array("b", [False] * 3)
        # flags[0] - stop_requested?
        # flags[1] - done?
        # flags[2] - true iff completed with no exception

    def start(self):
        """Start the job by invoking its .run() method asynchronously."""
        self._thread.start()

    def run(self):
        """Subclasses should override this to implement the Job's behavior."""
        raise NotImplementedError()

    def _run(self):
        """Private helper that wraps .run() and sets various exit flags."""
        try:
            if do_profiling.value:
                import cProfile
                import tempfile
                (fd, filename) = tempfile.mkstemp(suffix=".prof")
                print("Profile info: {}".format(filename))
                cProfile.runctx("self.run()", globals(), locals(), filename=filename)
            else:
                self.run()
            self._flags[2] = True
        except Exception as e:
            import traceback
            traceback.print_exc()
        self._flags[1] = True

    @property
    def stop_requested(self):
        """True if the job has been asked to stop.

        The implementation of .run() should check this periodically and return
        when it becomes True."""
        return self._flags[0]

    @property
    def done(self):
        """True if the job has stopped."""
        return self._flags[1] or (self._thread.exitcode is not None)

    @property
    def successful(self):
        """True if the job has stopped without throwing an uncaught exception."""
        return self._flags[2]

    def request_stop(self):
        """Request a graceful stop.

        Causes this Job's .stop_requested property to become True.

        Clients can call .join() to wait for the job to wrap up.
        """
        print("requesting stop for {}".format(self))
        self._flags[0] = True

    def join(self, timeout=None):
        """Wait for the job to finish and clean up its resources.

        This procedure may be called more than once, even on an already-joined
        Job.

        If `timeout` is provided, this procedure waits roughly `timeout`
        seconds at most.

        This procedure always returns None.  If a timeout is provided, clients
        should check the .done property to determine whether the job indeed
        stopped.

        NOTE: If a timeout was provided and the .done property was true after
        completion, clients MUST call .join() again to ensure that the Job's
        resources are properly cleaned up.  This is because the Job may have
        finished AFTER the call to .join() timed out but BEFORE the call to
        .done completed.

        Example of proper usage:

            job.join(timeout=1)
            if job.done:
                job.join()
                # the job is now complete and cleaned-up
            else:
                # the job is still running
        """
        self._thread.join(timeout=timeout)

    def kill(self):
        """Stop this job forcefully.

        This is implemented using the `Process.terminate()` procedure in the
        `multiprocessing` module.  There are two important caveats:

         - Clients should still call .join() afterwards to clean up the Job.
         - If this Job spawned any Jobs of its own that it did not join, then
           those jobs are now lost and can never be cleaned up.
         - If this Job was killed while it was putting an object into a Queue
           or SafeQueue or writing data to a pipe, then the queue or pipe may
           become corrupted and unusable by the parent process.
         - If this Job had acquired a shared lock, then it will not release the
           lock and killing it may lead to deadlocks.
        """
        self._thread.terminate()

    @property
    def pid(self):
        """Get the process ID of the process running this Job.

        Clients should not call this before .start() or after .join().
        """
        return self._thread.pid

def stop_jobs(jobs):
    """Call request_stop() on each job and wait for them to finish.

    This procedure also calls .join() on each job to clean up its resources.
    """

    jobs = list(jobs)
    for j in jobs:
        j.request_stop()

    while jobs:

        for j in jobs:
            j.join(timeout=1)
        done_jobs, jobs = partition(jobs, lambda j: j.done)
        for j in done_jobs:
            # need to do this because they might have finished AFTER the .join
            # timed out and BEFORE the .done check
            j.join()

        if jobs:
            print("Waiting on {} jobs...".format(len(jobs)))
            for j in jobs:
                print("  --> {} [pid={}]".format(j, j.pid))

class SafeQueue(object):
    """A queue for collecting results from Jobs.

    The multiprocessing.Queue class and its cousins come with a lot of caveats!
    Use this class if you want to worry less. Specifically:
        - This queue does not need to be drained to guarantee termination of
          child processes. From the docs [1]:
            > ... if a child process has put items on a queue (and it has not used
            > JoinableQueue.cancel_join_thread), then that process will not terminate
            > until all buffered items have been flushed to the pipe.
          This queue uses an auxiliary thread to solve this problem.
    However:
        - This queue needs to be closed.
    Proper usage example:
        with SafeQueue() as q:
            # spawn processes to insert items into q
            # get items from q
            # join spawned processes

    [1]: https://docs.python.org/3/library/multiprocessing.html#pipes-and-queues
    """
    def __init__(self, queue_to_wrap=None):
        if queue_to_wrap is None:
            queue_to_wrap = Queue()
        self.q = queue_to_wrap
        self.sideq = PlainQueue()
        self.stop_requested = False
    def __enter__(self, *args, **kwargs):
        self.thread = threading.Thread(target=self._copy_items, daemon=True)
        self.thread.start()
        return self
    def __exit__(self, *args, **kwargs):
        print("Stopping SafeQueue...")
        self.stop_requested = True
        self.thread.join()
        print("Done!")
    def _copy_items(self):
        while not self.stop_requested:
            try:
                self.sideq.put(self.q.get(timeout=1), timeout=1)
            except Empty:
                pass
            except Full:
                pass
    def put(self, item, block=False, timeout=None):
        return self.q.put(item, block=block, timeout=timeout)
    def get(self, block=False, timeout=None):
        return self.sideq.get(block=block, timeout=timeout)
    def drain(self, block=False, timeout=None):
        """
        Remove all elements currently in the queue and put them in a list,
        in the order they would have been returned by .get().

        If block=False (the default), then the timeout is ignored and this
        method may return an empty list.

        If block=True, then this function blocks until at least one element is
        available. If a timeout is also provided, then a queue.Empty exception
        is raised if no element is available in the given number of seconds.
        """
        res = []
        if block:
            res.append(self.get(block=True, timeout=timeout))
        while True:
            try:
                res.append(self.get(block=False))
            except Empty:
                return res
