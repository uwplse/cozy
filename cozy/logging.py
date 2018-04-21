from contextlib import contextmanager
import datetime

from cozy.opts import Option

verbose = Option("verbose", bool, False)

_task_stack = []

def log(string):
    if verbose.value:
        print(string)

def task_begin(name, **kwargs):
    if not verbose.value:
        return
    indent = "  " * len(_task_stack)
    log("{indent}{name}{maybe_kwargs}...".format(
        indent = indent,
        name   = name,
        maybe_kwargs = (" [" + ", ".join("{}={}".format(k, v) for k, v in kwargs.items()) + "]") if kwargs else ""))
    start = datetime.datetime.now()
    _task_stack.append((name, start))

def task_end():
    if not verbose.value:
        return
    end = datetime.datetime.now()
    name, start = _task_stack.pop()
    indent = "  " * len(_task_stack)
    log("{indent}Finished {name} [duration={duration:.3}s]".format(indent=indent, name=name, duration=(end-start).total_seconds()))

@contextmanager
def task(name, **kwargs):
    yield task_begin(name, **kwargs)
    task_end()

def event(name):
    if not verbose.value:
        return
    indent = "  " * len(_task_stack)
    log("{indent}{name}".format(indent=indent, name=name))
