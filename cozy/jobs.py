import threading
import time

from cozy.timeouts import Timeout

class Job(object):
    def __init__(self):
        self._thread = threading.Thread(target=self._run, daemon=True)
        self.stop_requested = False
        self.result = None
        self.done = False
        self.successful = False
    def start(self):
        self._thread.start()
    def _run(self):
        try:
            self.result = self.run()
            self.successful = True
        except Exception as e:
            import traceback
            traceback.print_exc()
        self.done = True
    def run(self):
        raise NotImplementedError()
    def stop(self):
        self.stop_requested = True
        self._thread.join()
    def wait(self):
        self._thread.join()
        return self.result

def wait_any(jobs : [Job], timeout : Timeout) -> Job:
    """
    Wait for at least one job to complete. Return the job that completed.
    """
    while True:
        timeout.check()
        for job in jobs:
            if job.done:
                return job
        time.sleep(0.1)
