from __future__ import print_function
from functools import total_ordering, wraps
import re
import sys
import os
import io
import inspect

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
        for k, t in ty.items():
            assert k in value, "{} is missing key {}".format(value_name, repr(k))
            check_type(value[k], t, "{}[{}]".format(value_name, repr(k)))
    elif type(ty) is set:
        assert type(value) is set, "{} has type {}, not {}".format(value_name, type(value).__name__, "set")
        subty, = ty
        for i in range(len(value)):
            check_type(value[i], subty, value_name)
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

def split(iter, p):
    t = []
    f = []
    for x in iter:
        if p(x):
            t.append(x)
        else:
            f.append(x)
    return (t, f)

def declare_case(supertype, name, attrs=()):
    """
    Usage:
        CaseName = declare_case(SuperType, "CaseName", ["member1", ...])

    Creates a new class (CaseName) that is a subclass of SuperType and has all
    the given members.
    """
    class T(supertype):
        def __init__(self, *args):
            assert len(args) == len(attrs), "{} expects {} args, was given {}".format(name, len(attrs), len(args))
            for attr, val in zip(attrs, args):
                setattr(self, attr, val)
        def __str__(self):
            return repr(self)
        def __repr__(self):
            return "{}({})".format(name, ", ".join("{}={}".format(attr, repr(val)) for attr, val in zip(attrs, self.children())))
        def children(self):
            return tuple(getattr(self, a) for a in attrs)
    T.__name__ = name
    return T

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
