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
"""

# builtins
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
from ordered_set import OrderedSet
from dictionaries import FrozenDict as _FrozenDict

def check_type(value, ty, value_name="value"):
    """
    Verify that the given value has the given type.
        value      - the value to check
        ty         - the type to check for, or None to do no checking
                     (for example, if types come from Python type annotations, and
                     the Python formal variable does not have a type annotation)
        value_name - the variable or expression that evaluates to `value`;
                     printed in diagnostic messages

    The type ty can be:
        str, int, float, or bytes - value must have this type
        [ty]                      - value must be a list of ty
        {k:v}                     - value must be a dict with keys of type k and values of type v
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
    """
    Use the @typechecked decorator on a function to perform run-time typechecking.
    The docstring for `check_type` describes how type annotations should look.
    """
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

def my_caller(up=0):
    """
    Returns a FrameInfo object describing the caller of the function that
    called my_caller.

    You might care about these properties of the FrameInfo object:
        .filename
        .function
        .lineno

    The `up` parameter can be used to look farther up the call stack.  For
    instance, up=1 returns info about the caller of the caller of the function
    that called my_caller.
    """
    stack = inspect.stack()
    return stack[up+2] # caller of caller of this function

def _size(x):
    """Compute the size of an ADT.

    This function uses a work stack rather than recursion, making it safe for
    use on very large or stick-like trees.

    See ADT.size (the public interface for this function) for more information
    about exactly what this function returns.
    """
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

# _protect helps to help guard against infinite recursion.
# Since it is global, locking uses seems wise.
_protect = set()
_protect_lock = threading.RLock()

@total_ordering
class ADT(object):
    """An algebraic data type (ADT).

    This class is not abstract, but it is not useful on its own; it is a parent
    for many useful types, especially syntax trees.

    ADTs are comparable (==, <, etc.), hashable (assuming they do not have
    lists or dictionaries as children), and pickle-able.

    Important methods:
        - children
        - size

    See also:
        - Visitor
    """

    def children(self):
        return ()
    def size(self):
        """Compute the size of an ADT.

        The size is 1 + sum(child sizes).  For the purposes of size computation,
        lists and tuples count as ADTs whose children are their elements.
        Dictionaries count as ADTs whose children are their items (key-value
        pairs).  All other types (e.g. strings and ints) are size 1.
        """
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
        """Call the method named "visit_TYPE" where TYPE is type(x)."""
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

_name_counter = Value(ctypes.c_uint64, 0)

def fresh_name(hint : str = "name", omit : {str} = ()) -> str:
    """Generate a new name.

    The returned name is guaranteed to be distinct from all names previously
    returned by `fresh_name` (even across threads and forked processes), and
    is is also guaranteed to be distinct from all names in `omit`.

    The `hint` parameter will be used in the generated name.
    """
    name = None
    with _name_counter.get_lock():
        i = _name_counter.value
        while name is None or name in omit:
            name = "_{}{}".format(hint, i)
            i += 1
        _name_counter.value = i
    return name

def capitalize(s):
    """Return a new string like s, but with the first letter capitalized."""
    return (s[0].upper() + s[1:]) if s else s

def product(iter):
    """Return the product of all the elements of iter, which should be numbers."""
    p = 1
    for x in iter:
        p *= x
    return p

@contextmanager
def AtomicWriteableFile(dst, mode="w"):
    """A writeable file handle that does not overwrite until it is closed.

    Usage:

        with AtomicWriteableFile(path) as f:
            ... f.write(...) ...

    This protects against errors that might happen while writing the file. If
    this object is closed due to an exception, it does not write any output to
    the destination path.
    """
    tmp_fd, tmp_path = tempfile.mkstemp(text=True)
    with os.fdopen(tmp_fd, mode) as f:
        yield f
        os.fsync(tmp_fd)
    shutil.move(src=tmp_path, dst=dst)

def open_maybe_stdin(f : str, mode="r"):
    """Open file f, or open standard input if f is "-".

    In any case, the caller is responsible for closing the returned handle.
    The safest usage of this function is

        with open_maybe_stdin(path) as f:
            ...
    """
    if f == "-":
        return os.fdopen(os.dup(sys.stdin.fileno()), mode)
    return open(f, mode)

def open_maybe_stdout(f : str, mode="w"):
    """Open file f, or open standard output if f is "-".

    If this function would open a regular file for writing, it returns an
    AtomicWriteableFile for safety.

    In any case, the caller is responsible for closing the returned handle.
    The safest usage of this function is

        with open_maybe_stdout(path) as f:
            ...
    """
    if f == "-":
        return os.fdopen(os.dup(sys.stdout.fileno()), mode)
    return AtomicWriteableFile(f, mode)

def unique(iter):
    """
    Yields a stream of deduplicated elements.
    Elements are returned in the same order as the input iterator.
    """
    yield from OrderedSet(iter)

def partition(iter, pred):
    """Split iter into two lists based on a test predicate.

    Returns (trues, falses) where "trues" are the elements from iter for
    which pred returns true, and "falses" are the ones for which pred returns
    false.
    """
    trues = []
    falses = []
    for x in iter:
        (trues if pred(x) else falses).append(x)
    return (trues, falses)

def pick_to_sum(n, total_size):
    """
    Enumerate all the ways to pick N positive integers that sum to total_size.

    Formally: yields all tuples ETRUE where len(ETRUE) = N and sum(ETRUE) = total_size.
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
    """
    Return a list or tuple containing the elements of iter.
    If iter is already a list or tuple, it returns iter.
    """
    if isinstance(iter, list) or isinstance(iter, tuple):
        return iter
    return list(iter)

def intersects(s1 : set, s2 : set):
    """Return true if the intersection of s1 and s2 is non-empty."""
    if len(s1) > len(s2):
        s1, s2 = s2, s1
    return any(x in s2 for x in s1)

@contextmanager
def save_property(x, prop_name):
    old_val = getattr(x, prop_name)
    yield
    setattr(x, prop_name, old_val)

def declare_case(supertype, name, attrs=()):
    """Create a new case for an ADT type.

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
    """
    Temporarily extend a dictionary with new values.
    Usage:
        my_dict = ...
        with extend_multi(my_dict, [(k1, v1), (k2, v2)]):
            # use my_dict
            # ...
        # values for my_dict[k1] and my_dict[k2] restored on exit
    """
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
        # value for my_dict[k] restored on exit
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
    """Returns the file contents as a single string."""
    with open(filename, "r") as f:
        return f.read()

def find_one(iter, pred=lambda x: True):
    for x in iter:
        if pred(x):
            return x
    return None

def exists(iter, pred=lambda x: True):
    for x in iter:
        if pred(x):
            return True
    return False

def divide_integers_and_round_up(x, y):
    assert x > 0
    assert y > 0
    return ((x - 1) // y) + 1

def integer_log2_round_up(x):
    """
    Returns the number of bits required to represent `x` distinct values---i.e.
    log2(x) rounded up.
    """
    assert x > 0
    bits = 1
    representable = 2 ** bits
    while representable < x:
        bits += 1
        representable *= 2
    return bits

def identity_func(x):
    return x

def compare_with_lt(x, y):
    """
    Comparator function that promises only to use the `<` binary operator
    (not `>`, `<=`, etc.)
    See also: `functools.cmp_to_key` if you plan to use this with `sorted`.
    """
    if x < y:
        return -1
    elif y < x:
        return 1
    else:
        return 0

class StopException(Exception):
    """
    Used to indicate that a process should stop operation.
    """
    pass
