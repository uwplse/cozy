from collections import defaultdict, OrderedDict, MutableSet
from functools import total_ordering, wraps
import sys
import os
import inspect
from multiprocessing import Value
import ctypes
import tempfile
import shutil

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
        assert type(value) is tuple, "{} has type {}, not {}".format(value_name, type(value).__name__, "tuple")
        assert len(value) == len(ty), "{} has {} entries, not {}".format(value_name, len(value), len(ty))
        for v, t, i in zip(value, ty, range(len(value))):
            check_type(v, t, "{}[{}]".format(value_name, i))
    elif type(ty) is list:
        assert type(value) is list, "{} has type {}, not {}".format(value_name, type(value).__name__, "list")
        for i in range(len(value)):
            check_type(value[i], ty[0], "{}[{}]".format(value_name, i))
    elif type(ty) is dict:
        assert type(value) is dict, "{} has type {}, not {}".format(value_name, type(value).__name__, "dict")
        ((kt, vt),) = ty.items()
        for k, v in value.items():
            check_type(k, kt, value_name)
            check_type(v, vt, "{}[{}]".format(value_name, k))
    elif type(ty) is set:
        assert type(value) is set, "{} has type {}, not {}".format(value_name, type(value).__name__, "set")
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

@total_ordering
class ADT(object):
    def __init__(self):
        self._protect = False
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
        return repr(self)
    def __repr__(self):
        if not hasattr(self, "_protect"):
            self._protect = False
        if self._protect:
            return "<<recursive>>"
        self._protect = True
        try:
            return "{}({})".format(type(self).__name__, ", ".join(repr(child) for child in self.children()))
        finally:
            self._protect = False
    def __hash__(self):
        return hash(self.children())
    def __eq__(self, other):
        return type(self) is type(other) and self.children() == other.children()
    def __ne__(self, other):
        return not self.__eq__(other)
    def __lt__(self, other):
        return (self.children() < other.children()) if (type(self) is type(other)) else (type(self).__name__ < type(other).__name__)

class Visitor(object):
    def visit(self, x, *args, **kwargs):
        t = type(x)
        first_visit_func = None
        while t is not None:
            visit_func = "visit_{}".format(t.__name__)
            first_visit_func = first_visit_func or visit_func
            if not hasattr(self, visit_func):
                if t is object:
                    break
                else:
                    t = t.__base__
                    continue
            return getattr(self, visit_func)(x, *args, **kwargs)
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

@total_ordering
class FrozenDict(dict):
    """
    Immutable dictionary that is hashable (suitable for use in sets/maps)
    """
    def __init__(self, d):
        super().__init__(d)
        self.hc = None
    def __setitem__(self, k, v):
        raise Exception("immutable")
    def __delitem__(self, k):
        raise Exception("immutable")
    def __hash__(self):
        if self.hc is None:
            self.hc = hash(tuple(sorted(self.items())))
        return self.hc
    def __lt__(self, other):
        return tuple(sorted(self.items())) < tuple(sorted(other.items()))

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
def fresh_name(hint="name"):
    with _i.get_lock():
        _i.value += 1
        return "_{}{}".format(hint, _i.value)

def capitalize(s):
    return (s[0].upper() + s[1:]) if s else s

def product(iter):
    p = 1
    for x in iter:
        p *= x
    return p

def all_distinct(iter):
    elems = iter if isinstance(iter, list) else list(iter)
    distinct_elems = set(elems)
    return len(elems) == len(distinct_elems)

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

def split(iter, p):
    t = []
    f = []
    for x in iter:
        if p(x):
            t.append(x)
        else:
            f.append(x)
    return (t, f)

class OrderedSet(MutableSet):
    """
    Set implementation that remembers the insertion order of elements.
    Source: https://code.activestate.com/recipes/576694/
    """

    def __init__(self, iterable=None):
        self.end = end = []
        end += [None, end, end]         # sentinel node for doubly linked list
        self.map = {}                   # key --> [key, prev, next]
        if iterable is not None:
            self |= iterable

    def __len__(self):
        return len(self.map)

    def __contains__(self, key):
        return key in self.map

    def add(self, key):
        if key not in self.map:
            end = self.end
            curr = end[1]
            curr[2] = end[1] = self.map[key] = [key, curr, end]

    def discard(self, key):
        if key in self.map:
            key, prev, next = self.map.pop(key)
            prev[2] = next
            next[1] = prev

    def __iter__(self):
        end = self.end
        curr = end[2]
        while curr is not end:
            yield curr[0]
            curr = curr[2]

    def __reversed__(self):
        end = self.end
        curr = end[1]
        while curr is not end:
            yield curr[0]
            curr = curr[1]

    def pop(self, last=True):
        if not self:
            raise KeyError('set is empty')
        key = self.end[1][0] if last else self.end[2][0]
        self.discard(key)
        return key

    def __repr__(self):
        if not self:
            return '%s()' % (self.__class__.__name__,)
        return '%s(%r)' % (self.__class__.__name__, list(self))

    def __eq__(self, other):
        if isinstance(other, OrderedSet):
            return len(self) == len(other) and list(self) == list(other)
        return set(self) == set(other)

def unique(iter, key=lambda x: x):
    """
    Yields a stream of deduplicated elements. If the 'key' parameter is
    provided, elements x are deduplicated according to key(x). When duplicates
    are found, the first element in the iterable is kept and others are
    dropped. Elements are returned in the same order as the input iterator.
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
    for size in range(1, total_size - n + 2):
        for rest in pick_to_sum(n - 1, total_size - size):
            yield (size,) + rest

def cross_product(iters, i=0):
    """
    Take the cross product of a finite set of possibly-infinite iterators.
    """
    if i == len(iters):
        yield ()
    if i >= len(iters):
        return
    for x in iters[i]:
        for rest in cross_product(iters, i + 1):
            yield (x,) + rest

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
    def __init__(self, *args):
        assert len(args) == len(attrs), "{} expects {} args, was given {}".format(name, len(attrs), len(args))
        for attr, val in zip(attrs, args):
            setattr(self, attr, val)
    def children(self):
        return tuple(getattr(self, a) for a in attrs)
    t = type(name, (supertype,), {
        "__init__": __init__,
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
