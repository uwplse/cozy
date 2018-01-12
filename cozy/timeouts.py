import datetime
import time

class TimeoutException(Exception):
    pass

class Timeout(object):
    def __init__(self, duration):
        self.duration = duration
        self.expiration = datetime.datetime.now() + duration if duration is not None else None
    def is_timed_out(self):
        return self.expiration is not None and datetime.datetime.now() > self.expiration
    def check(self):
        if self.is_timed_out():
            raise TimeoutException()
    def remaining(self):
        return self.expiration - datetime.datetime.now()
    def wait(self):
        """
        Blocks until self.is_timed_out()
        """
        if self.expiration is None:
            while True:
                time.sleep(60)
        else:
            while not self.is_timed_out():
                time.sleep(self.remaining().total_seconds())
