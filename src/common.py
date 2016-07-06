from functools import total_ordering, wraps
import re
import sys
import os
import io

@total_ordering
class ADT(object):
    def children(self):
        return ()
    def size(self):
        s = 1
        for child in self.children():
            if isinstance(child, ADT):
                s += child.size()
        return s
    def contains_subtree(self, tree):
        if self == tree:
            return True
        for child in self.children():
            if isinstance(child, ADT) and child.contains_subtree(tree):
                return True
    def __str__(self):
        return "{}({})".format(type(self).__name__, ", ".join(str(child) for child in self.children()))
    def __hash__(self):
        return hash(self.children())
    def __eq__(self, other):
        return type(self) is type(other) and self.children() == other.children()
    def __lt__(self, other):
        return (self.children() < other.children()) if (type(self) is type(other)) else (type(self).__name__ < type(other).__name__)

_i = 0
def fresh_name(hint="name"):
    global _i
    _i += 1
    return "_{}{}".format(hint, _i)

def capitalize(s):
    return (s[0].upper() + s[1:]) if s else s

_START_OF_LINE = re.compile(r"^", re.MULTILINE)
def indent(i, s):
    return _START_OF_LINE.sub(i, s)

def open_maybe_stdout(f):
    if f is None:
        return io.StringIO()
    if f == "-":
        return os.fdopen(os.dup(sys.stdout.fileno()), "w")
    return open(f, "w")

def memoize(f):
    # Someday if we upgrade to Python 3 this can be replaced with
    # functools.lru_cache(...).

    cache = dict()

    @wraps(f)
    def wrapper(*args, **kwargs):
        k = (tuple(args), tuple(kwargs.items()))
        if k in cache:
            return cache[k]
        result = f(*args, **kwargs)
        cache[k] = result
        return result

    return wrapper
