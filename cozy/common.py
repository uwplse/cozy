"""Utility functions and classes not found in the standard libraries.

Important functions and classes:
 - @typechecked: decorator to perform runtime typechecking
 - ADT: top-level class for algebraic data types
 - declare_case: create a new subclass of an ADT
 - Visitor: top-level class for visitors over ADTs
 - fresh_name: generate a never-before-seen name (string)

Extra collection types:
 - OrderedSet: complements Python's OrderedDict
 - FrozenDict: a hashable immutable dictionary
 - OrderedDefaultDict: a fusion of Python's OrderedDict and defaultdict
"""

# builtins
from collections import defaultdict, OrderedDict
from contextlib import contextmanager
from functools import total_ordering, wraps
import sys
import os
import inspect
from multiprocessing import Value
import threading
import ctypes
import tempfile
import shutil

# 3rd party
from oset import oset as OrderedSet
from dictionaries import FrozenDict as _FrozenDict

def check_type(value, ty, value_name="value"):
    """
    Verify that the given value has the given type.
        value      - the value to check
        ty         - the type to check for
        value_name - the name to print for debugging

    The type ty can be:
        str, int, float, or bytes - value must have this type
        [ty]                      - value must be a list of ty
        {k:ty,...}                - value must be a dict with keys of the given types
    """

    if ty is None:
        pass
    elif type(ty) is tuple:
        assert isinstance(value, tuple), "{} has type {}, not {}".format(value_name, type(value).__name__, "tuple")
        assert len(value) == len(ty), "{} has {} entries, not {}".format(value_name, len(value), len(ty))
        for v, t, i in zip(value, ty, range(len(value))):
            check_type(v, t, "{}[{}]".format(value_name, i))
    elif type(ty) is list:
        assert isinstance(value, list), "{} has type {}, not {}".format(value_name, type(value).__name__, "list")
        for i in range(len(value)):
            check_type(value[i], ty[0], "{}[{}]".format(value_name, i))
    elif type(ty) is dict:
        assert isinstance(value, dict), "{} has type {}, not {}".format(value_name, type(value).__name__, "dict")
        ((kt, vt),) = ty.items()
        for k, v in value.items():
            check_type(k, kt, value_name)
            check_type(v, vt, "{}[{}]".format(value_name, k))
    elif type(ty) is set:
        assert isinstance(value, set) or isinstance(value, OrderedSet), "{} has type {}, not {}".format(value_name, type(value).__name__, "set")
        subty, = ty
        for x in value:
            check_type(x, subty, "{} in {}".format(x, value_name))
    else:
        assert isinstance(value, ty), "{} has type {}, not {}".format(value_name, type(value).__name__, ty.__name__)

def typechecked(f):
    argspec = inspect.getfullargspec(f)
    annotations = f.__annotations__
    @wraps(f)
    def g(*args, **kwargs):
        for argname, argval in zip(argspec.args, args):
            check_type(argval, annotations.get(argname), argname)
        for argname, argval in kwargs.items():
            check_type(argval, annotations.get(argname), argname)
        ret = f(*args, **kwargs)
        check_type(ret, annotations.get("return"), "return")
        return ret
    return g

def match(value, binders):

    def match_into(value, pattern, out):
        if isinstance(pattern, str):
            if pattern in out:
                return out[pattern] == value
            else:
                out[pattern] = value
                return True
        elif pattern is any:
            return True
        elif isinstance(pattern, ADT):
            if isinstance(value, type(pattern)):
                for i in range(len(pattern.children())):
                    if not match_into(value.children()[i], pattern.children()[i], out):
                        return False
                return True
            else:
                return False
        else:
            return value == pattern

    for pattern, callback in binders:
        out = { }
        if match_into(value, pattern, out):
            return callback(**out)

    return None

# _protect helps to help guard against infinite recursion
# Since it is global, locking uses seems wise.
_protect = set()
_protect_lock = threading.RLock()

def my_caller(up=0):
    """
    Returns an info object of caller function.
    You might care about these properties:
        .filename
        .function
        .lineno
    """
    stack = inspect.stack()
    frame = stack[up+2] # caller of caller of this function
    frame = frame[0]
    return inspect.getframeinfo(frame)

def _size(x):
    wq = [x]
    res = 0
    while wq:
        x = wq.pop()
        res += 1
        if isinstance(x, ADT):
            wq.extend(x.children())
        elif isinstance(x, list) or isinstance(x, tuple):
            wq.extend(x)
        elif isinstance(x, dict):
            wq.extend(x.items())
    return res

class No(object):
    """A falsy object with a message.

    This is useful if you want to return False with an associated reason."""
    def __init__(self, msg):
        self.msg = msg
    def __bool__(self):
        return False
    def __str__(self):
        return "no: {}".format(self.msg)
    def __repr__(self):
        return "No({!r})".format(self.msg)

@total_ordering
class ADT(object):
    def children(self):
        return ()
    def size(self):
        return _size(self)
    def contains_subtree(self, tree):
        if self == tree:
            return True
        for child in self.children():
            if isinstance(child, ADT) and child.contains_subtree(tree):
                return True
    def __str__(self):
        return repr(self)
    def __repr__(self):
        my_id = id(self)
        with _protect_lock:
            if my_id in _protect:
                return "<<recursive>>"
            _protect.add(my_id)
            try:
                return "{}({})".format(type(self).__name__, ", ".join(repr(child) for child in self.children()))
            finally:
                # remove my_id, but do not throw an exception on failure
                _protect.difference_update({my_id})
    def __hash__(self):
        if not hasattr(self, "_hash"):
            self._hash = hash(self.children())
        return self._hash
    def __getstate__(self):
        d = dict(self.__dict__)
        if "_hash" in d:
            del d["_hash"]
        if hasattr(self, "__slots__"):
            for a in self.__slots__:
                d[a] = getattr(self, a)
        return d
    def __setstate__(self, d):
        for k, v in d.items():
            setattr(self, k, v)
    def __eq__(self, other):
        if self is other: return True
        return type(self) is type(other) and self.children() == other.children()
    def __ne__(self, other):
        return not self.__eq__(other)
    def __lt__(self, other):
        if self is other: return False
        return (self.children() < other.children()) if (type(self) is type(other)) else (type(self).__name__ < type(other).__name__)

class Visitor(object):
    def visit(self, x, *args, **kwargs):
        t = type(x)
        first_visit_func = None
        while t is not None:
            visit_func = "visit_" + t.__name__
            first_visit_func = first_visit_func or visit_func
            f = getattr(self, visit_func, None)
            if f is None:
                if t is object:
                    break
                else:
                    t = t.__base__
                    continue
            return f(x, *args, **kwargs)
        print("Warning: {} does not implement {}".format(self, first_visit_func), file=sys.stderr)

def ast_find(ast, pred):
    class V(Visitor):
        def visit(self, x):
            if pred(x):
                yield x
            yield from super().visit(x)
        def visit_ADT(self, x):
            for child in x.children():
                yield from self.visit(child)
        def visit_list(self, x):
            for child in x:
                yield from self.visit(child)
        def visit_tuple(self, x):
            return self.visit_list(x)
        def visit_object(self, x):
            return ()
    return V().visit(ast)

def ast_find_one(ast, pred):
    for match in ast_find(ast, pred):
        return match
    return None

def ast_replace(haystack, pred, repl_func):
    class V(Visitor):
        def visit(self, x):
            if pred(x):
                return repl_func(x)
            return super().visit(x)
        def visit_ADT(self, x):
            new_children = tuple(self.visit(child) for child in x.children())
            return type(x)(*new_children)
        def visit_list(self, x):
            return [self.visit(child) for child in x]
        def visit_tuple(self, x):
            return tuple(self.visit(child) for child in x)
        def visit_object(self, x):
            return x
    return V().visit(haystack)

def ast_replace_ref(haystack, needle, replacement):
    return ast_replace(haystack,
        lambda x: x is needle,
        lambda x: replacement)

# Monkey-patch OrderedSet to avoid infinite loops during interpreter shutdown.
# The implementors of the library implemented __del__, a dangerous magic method
# that runs when an object is garbage-collected.  This can go horribly awry in
# the following complex---but possible---set of circumstances:
#   (1) Several OrderedSets are queued for garbage collection simultaneously
#   (2) The hash codes of some of the elements of some OrderedSet A depend on
#       the elements present in a different OrderedSet B (this can be
#       reasonable: while OrderedSets are mutable, hashing tuple(ordered_set)
#       really ought to be safe)
#   (3) The garbage collector decides to invoke __del__ on B first
#   (4) The change in hash code results in an infinite loop when calling
#       __del__ on A, which now contains an element that it cannot find via
#       hash lookup.
# Removing the __del__ method is perfectly safe: Python's cycle collector will
# kick in and do the job that this is trying to achieve.
del OrderedSet.__del__

@total_ordering
class FrozenDict(_FrozenDict):
    """
    Immutable dictionary that is hashable (suitable for use in sets/maps)
    and orderable (supports <, >, etc).
    """

    def __lt__(self, other):
        return tuple(sorted(self.items())) < tuple(sorted(other.items()))

    def __repr__(self):
        return "FrozenDict({!r})".format(list(self.items()))

_MISSING = object()
class OrderedDefaultDict(OrderedDict):
    def __init__(self, factory):
        super().__init__()
        self.factory = factory
    def __missing__(self, k):
        v = self.get(k, _MISSING)
        if v is _MISSING:
            v = self.factory()
            self[k] = v
        return v

def nested_dict(n, t):
    if n <= 0:
        return t()
    return OrderedDefaultDict(lambda: nested_dict(n-1, t))

_i = Value(ctypes.c_uint64, 0)
def fresh_names(n : int, hint : str = "name", omit : {str} = None) -> [str]:
    if omit is None:
        omit = ()

    res = []
    with _i.get_lock():
        i = _i.value
        for _ in range(n):
            name = None
            while name is None or name in omit:
                name = "_{}{}".format(hint, i)
                i += 1
            res.append(name)
        _i.value = i

    return res

def fresh_name(hint="name", omit=None):
    return fresh_names(1, hint=hint, omit=omit)[0]

def capitalize(s):
    return (s[0].upper() + s[1:]) if s else s

def product(iter):
    p = 1
    for x in iter:
        p *= x
    return p

class AtomicWriteableFile(object):
    def __init__(self, dst):
        self.dst = dst
        tmp_fd, tmp_path = tempfile.mkstemp(text=True)
        self.tmp_fd = tmp_fd
        self.tmp_file = os.fdopen(tmp_fd, "w")
        self.tmp_path = tmp_path
    def __enter__(self, *args, **kwargs):
        return self
    def __exit__(self, *args, **kwargs):
        os.fsync(self.tmp_fd)
        self.tmp_file.close() # also closes self.tmp_fd
        shutil.move(src=self.tmp_path, dst=self.dst)
    def write(self, thing):
        self.tmp_file.write(thing)

def open_maybe_stdout(f):
    if f == "-":
        return os.fdopen(os.dup(sys.stdout.fileno()), "w")
    return AtomicWriteableFile(f)

def split(iter, p):
    t = []
    f = []
    for x in iter:
        if p(x):
            t.append(x)
        else:
            f.append(x)
    return (t, f)

def unique(iter):
    """
    Yields a stream of deduplicated elements.
    Elements are returned in the same order as the input iterator.
    """
    yield from OrderedSet(iter)

def partition(iter, p):
    t = []
    f = []
    for x in iter:
        (t if p(x) else f).append(x)
    return (t, f)

def pick_to_sum(n, total_size):
    """
    Enumerate all the ways to pick N integers greater than zero that sum to
    total_size.

    Formally: yields all tuples T where len(T) = N and sum(T) = total_size.
    """
    if n == 0:
        if total_size == 0:
            yield ()
        return
    if n == 1:
        yield (total_size,)
        return
    for size in range(0, total_size + 1):
        for rest in pick_to_sum(n - 1, total_size - size):
            yield (size,) + rest

def make_random_access(iter):
    if isinstance(iter, list) or isinstance(iter, tuple):
        return iter
    return list(iter)

def intersects(s1 : set, s2 : set):
    if len(s1) > len(s2):
        s1, s2 = s2, s1
    return any(x in s2 for x in s1)

@contextmanager
def save_property(x, prop_name):
    old_val = getattr(x, prop_name)
    yield
    setattr(x, prop_name, old_val)

def group_by(iter, k, v=list):
    xs = defaultdict(list)
    for x in iter:
        xs[k(x)].append(x)
    res = defaultdict(lambda: v([]))
    for (key, val) in xs.items():
        res[key] = v(val)
    return res

def declare_case(supertype, name, attrs=()):
    """
    Usage:
        CaseName = declare_case(SuperType, "CaseName", ["member1", ...])

    Creates a new class (CaseName) that is a subclass of SuperType and has all
    the given members.
    """
    if not isinstance(attrs, tuple):
        attrs = tuple(attrs)
    def __init__(self, *args):
        assert len(args) == len(attrs), "{} expects {} args, was given {}".format(name, len(attrs), len(args))
        supertype.__init__(self)
        for attr, val in zip(attrs, args):
            setattr(self, attr, val)
    def children(self):
        return tuple(getattr(self, a) for a in attrs)
    t = type(name, (supertype,), {
        "__init__": __init__,
        "__slots__": attrs,
        "children": children })
    globals()[name] = t
    return t

class extend_multi(object):
    def __init__(self, d, items):
        self.things = [extend(d, k, v) for (k, v) in items]
    def __enter__(self, *args, **kwargs):
        for x in self.things:
            x.__enter__(*args, **kwargs)
    def __exit__(self, *args, **kwargs):
        for x in self.things:
            x.__exit__(*args, **kwargs)

class extend(object):
    """
    Temporarily extend a dictionary with a new value.
    Usage:
        my_dict = ...
        with extend(my_dict, k, new_val):
            # use my_dict
            # ...
    """
    NO_VAL = object()
    def __init__(self, d, k, v):
        self.d = d
        self.k = k
        self.new_val = v
        self.old_val = d.get(k, extend.NO_VAL)
    def __enter__(self, *args, **kwargs):
        self.d[self.k] = self.new_val
    def __exit__(self, *args, **kwargs):
        if self.old_val is extend.NO_VAL:
            del self.d[self.k]
        else:
            self.d[self.k] = self.old_val

def read_file(filename):
    with open(filename, "r") as f:
        return f.read()

def find_one(iter, p=lambda x: True):
    for x in iter:
        if p(x):
            return x
    return None

def exists(iter, p=lambda x: True):
    for x in iter:
        if p(x):
            return True
    return False

def divide_integers_and_round_up(x, y):
    assert x > 0
    assert y > 0
    return (x - 1) // y + 1

def integer_log2_round_up(x):
    """
    Returns the number of bits required to represent `x` distinct values---i.e.
    log2(x) rounded up.
    """
    assert x > 0
    i = 1
    p = 2 ** i
    while p < x:
        i += 1
        p *= 2
    return i

def identity_func(x):
    return x

def compare_with_lt(x, y):
    """
    Comparator function that promises only to use the `<` binary operator.
    See also: `functools.cmp_to_key` if you plan to use this with `sorted`
    """
    if x < y:
        return -1
    elif y < x:
        return 1
    else:
        return 0

def collapse_runs(it, split_at):
    """
    Collapse runs of elements [x_0, x_1, ...] in `it` such that
    `split_at(x_0, x_i)` returns false for all i > 1.

    This function returns a list of runs (i.e. a list of lists).

    For instance, to remove duplicates from a sorted list:
        l = [0, 0, 0, 1, 2, 2]
        l = collapse_runs(l, split_at=lambda x, y: x != y)
        # l is now [[0,0,0], [1], [2,2]]
    """
    l = make_random_access(it)
    if not l:
        return l, []
    prev = l[0]
    res = [[prev]]
    for i in range(1, len(l)):
        x = l[i]
        if split_at(prev, x):
            res.append([x])
        else:
            res[-1].append(x)
        prev = x
    return res

class StopException(Exception):
    """
    Used to indicate that a process should stop operation.
    """
    pass
