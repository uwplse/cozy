import collections
import functools
import datetime

class Task(object):
    def __init__(self, name, data=None):
        self.name = name
        self.data = data
    def __enter__(self, *args, **kwargs):
        task_begin(self.name, self.data)
    def __exit__(self, *args, **kwargs):
        task_end(self.name, self.data)

timestk = []
times = collections.defaultdict(datetime.timedelta)
counts = collections.defaultdict(int)

def task_begin(name, data):
    depth = len(timestk)
    # print(" " * depth + "starting {}".format(name))
    timestk.append(datetime.datetime.now())

def task_end(name, data):
    duration = datetime.datetime.now() - timestk[-1]
    del timestk[-1]
    depth = len(timestk)
    times[(name, data)] += duration
    counts[(name, data)] += 1
    if duration > datetime.timedelta(seconds=1):
        print(" " * depth + "finished {} ({:0.2f}s)".format(name, duration.total_seconds()))

def task(f):
    @functools.wraps(f)
    def g(*args, **kwargs):
        with Task(f.__name__):
            return f(*args, **kwargs)
    return g

def generator_task(f):
    @functools.wraps(f)
    def g(*args, **kwargs):
        with Task(f.__name__):
            yield from f(*args, **kwargs)
    return g

def inline_task(name, f):
    with Task(name):
        return f()
