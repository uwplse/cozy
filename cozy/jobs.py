from multiprocessing import Process, Array, Queue
from queue import Queue as PlainQueue, Empty
import time
import threading
import sys

from cozy.timeouts import Timeout
from cozy.opts import Option

do_profiling = Option("profile", bool, False, description="Profile Cozy itself")

class Job(object):
    def __init__(self):
        self._thread = Process(target=self._run, daemon=True)
        self._flags = Array("b", [False] * 3)
        # flags[0] - stop_requested?
        # flags[1] - done?
        # flags[2] - true iff completed with no exception
    def start(self):
        self._thread.start()
    def _run(self):
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
    def run(self):
        raise NotImplementedError()
    @property
    def stop_requested(self):
        return self._flags[0]
    @property
    def done(self):
        return self._flags[1]
    @property
    def successful(self):
        return self._flags[2]
    def request_stop(self):
        print("requesting stop for {}".format(self))
        self._flags[0] = True
    def join(self, timeout=None):
        self._thread.join(timeout=timeout)

def stop_jobs(jobs):
    jobs = list(jobs)
    for j in jobs:
        j.request_stop()
    for j in jobs:
        while True:
            j.join(timeout=30)
            if j.done:
                break
            print("job '{}' failed to stop in 30 seconds".format(j), file=sys.stderr)

class SafeQueue(object):
    """
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
        self.stop_requested = True
        self.thread.join()
    def _copy_items(self):
        while not self.stop_requested:
            try:
                self.sideq.put(self.q.get(timeout=0.5))
            except Empty:
                pass
    def put(self, item, block=False, timeout=None):
        return self.q.put(item, block=block, timeout=timeout)
    def get(self, block=False, timeout=None):
        return self.sideq.get(block=block, timeout=timeout)
    def drain(self, block=False, timeout=None):
        """
        Remove all elements currently in the queue and put them in a list.
        The first element in the list is the first element that would have
        been returned by .get(), the second is the second, and so on.

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
