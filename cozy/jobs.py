from multiprocessing import Process, Array, Queue
import time

from cozy.timeouts import Timeout

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
    def stop(self):
        self._flags[0] = True
        self._thread.join()
    def wait(self):
        self._thread.join()
