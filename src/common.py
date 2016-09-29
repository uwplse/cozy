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

_i = 0
def fresh_name(hint="name"):
    global _i
    _i += 1
    return "_{}{}".format(hint, _i)

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

def unique(iter, key=lambda x: x):
    """
    Yields a stream of deduplicated elements. If the 'key' parameter is
    provided, elements x are deduplicated according to key(x). When duplicates
    are found, the first element in the iterable is kept and others are
    dropped.
    """
    seen = set()
    for x in iter:
        k = key(x)
        if k not in seen:
            seen.add(k)
            yield x

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
        self._protect = False # prevent infinite recursion
    def __str__(self):
        return repr(self)
    def __repr__(self):
        if self._protect:
            return "<<recursive>>"
        self._protect = True
        try:
            return "{}({})".format(type(self).__name__, ", ".join("{}={}".format(attr, repr(val)) for attr, val in zip(attrs, self.children())))
        finally:
            self._protect = False
    def children(self):
        return tuple(getattr(self, a) for a in attrs)
    t = type(name, (supertype,), {
        "__init__": __init__,
        "__str__": __str__,
        "__repr__": __repr__,
        "children": children })
    globals()[name] = t
    return t

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
