from collections import UserDict, defaultdict, namedtuple
from functools import total_ordering, cmp_to_key, lru_cache
import itertools

from cozy.target_syntax import *
from cozy.syntax_tools import equal, pprint, free_vars, free_funcs, all_exps, purify
from cozy.common import FrozenDict, OrderedSet, extend
from cozy.typecheck import is_numeric, is_collection
from cozy.structures import extension_handler

@total_ordering
class Map(object):
    def __init__(self, type, default, items=()):
        self.type = type
        self._items = []
        for (k, v) in items:
            self[k] = v
        self.default = default
    def __setitem__(self, k, v):
        for i in range(len(self._items)):
            (kk, vv) = self._items[i]
            if eq(self.type.k, k, kk):
                self._items[i] = (kk, v)
                return
        # if not eq(self.type.v, v, self.default):
        self._items.append((k, v))
        # assert all(not eq(self.type.v, v, self.default) for (k, v) in self.items())
    def __getitem__(self, k):
        for i in range(len(self._items)):
            (kk, vv) = self._items[i]
            if eq(self.type.k, k, kk):
                return vv
        return self.default
    def items(self):
        yield from self._items
    def keys(self):
        for (k, v) in reversed(self._items):
            yield k
    def values(self):
        for (k, v) in self._items:
            yield v
    def _hashable(self):
        return (self.default,) + tuple(sorted(self._items))
    def __hash__(self):
        return hash(self._hashable())
    def __repr__(self):
        return "Map({}, {}, {})".format(repr(self.type), repr(self.default), repr(self._items))
    def __str__(self):
        return repr(self)
    def __lt__(self, other):
        return self._hashable() < other._hashable()
    def __eq__(self, other):
        return self._hashable() == other._hashable()

@total_ordering
class Bag(object):
    def __init__(self, iterable=()):
        self.elems = iterable if isinstance(iterable, tuple) else tuple(iterable)
    def __hash__(self):
        return hash(self.elems)
    def __add__(self, other):
        return Bag(self.elems + other.elems)
    def __eq__(self, other):
        return self.elems == other.elems
    def __lt__(self, other):
        return self.elems < other.elems
    def __len__(self):
        return len(self.elems)
    def __getitem__(self, i):
        return self.elems[i]
    def __bool__(self):
        return bool(self.elems)
    def __str__(self):
        return repr(self)
    def __repr__(self):
        return "Bag({})".format(repr(self.elems))
    def __contains__(self, x):
        return x in self.elems
    def __iter__(self):
        return iter(self.elems)

Handle = namedtuple("Handle", ["address", "value"])

LT = -1
EQ =  0
GT =  1
def cmp(t, v1, v2, deep=False):
    stk = [(t, v1, v2)]

    orig_deep = deep
    def cleardeep():
        nonlocal deep
        deep = False
    def resetdeep():
        nonlocal deep
        deep = orig_deep

    while stk:
        head = stk.pop()
        if hasattr(head, "__call__"):
            head()
            continue
        (t, v1, v2) = head

        if isinstance(t, THandle):
            if deep:
                stk.append((t.value_type, v1.value, v2.value))
            stk.append((INT, v1.address, v2.address))
        elif isinstance(t, TEnum):
            i1 = t.cases.index(v1)
            i2 = t.cases.index(v2)
            if i1 == i2: continue
            if i1 <  i2: return LT
            else:        return GT
        elif isinstance(t, TBag) or isinstance(t, TSet):
            # TODO: if deep, handle "the"?
            if deep:
                elems1 = list(v1)
                elems2 = list(v2)
            else:
                elems1 = list(sorted(v1))
                elems2 = list(sorted(v2))
            if len(elems1) < len(elems2): return LT
            if len(elems1) > len(elems2): return GT
            stk.extend(reversed([(t.t, x, y) for (x, y) in zip(elems1, elems2)]))
        elif isinstance(t, TMap):
            keys1 = Bag(v1.keys())
            keys2 = Bag(v2.keys())
            stk.extend(reversed([(t.v, v1[k], v2[k]) for k in sorted(keys1)]))
            stk.append(resetdeep)
            stk.append((TSet(t.k), keys1, keys2))
            stk.append(cleardeep)
            stk.append((t.v, v1.default, v2.default))
        elif isinstance(t, TTuple):
            stk.extend(reversed([(tt, vv1, vv2) for (tt, vv1, vv2) in zip(t.ts, v1, v2)]))
        elif isinstance(t, TList):
            stk.extend(reversed([(t.t, vv1, vv2) for (vv1, vv2) in zip(v1, v2)]))
            stk.append((INT, len(v1), len(v2)))
        elif isinstance(t, TRecord):
            stk.extend(reversed([(ft, v1[f], v2[f]) for (f, ft) in t.fields]))
        else:
            if   v1 == v2: continue
            elif v1 <  v2: return LT
            else:          return GT
    return EQ

def eq(t, v1, v2):
    return cmp(t, v1, v2) == EQ

def eval(e, env, *args, **kwargs):
    return eval_bulk(e, (env,), *args, **kwargs)[0]

@lru_cache(maxsize=None)
def mkval(type : Type):
    """
    Produce an arbitrary value of the given type.
    eval(construct_value(t), {}) == mkval(t)
    """
    return eval(construct_value(type), {})

@typechecked
def construct_value(t : Type) -> Exp:
    """
    Construct an arbitrary expression e of the given type.
    eval(construct_value(t), {}) == mkval(t)
    """
    if is_numeric(t):
        e = ENum(0)
    elif t == BOOL:
        e = F
    elif t == STRING:
        e = EStr("")
    elif is_collection(t):
        e = EEmptyList()
    elif isinstance(t, TTuple):
        e = ETuple(tuple(construct_value(tt) for tt in t.ts))
    elif isinstance(t, TRecord):
        e = EMakeRecord(tuple((f, construct_value(tt)) for (f, tt) in t.fields))
    elif isinstance(t, TEnum):
        e = EEnumEntry(t.cases[0])
    elif isinstance(t, THandle):
        e = EHandle(construct_value(INT), construct_value(t.value_type))
    elif isinstance(t, TNative):
        e = ENative(construct_value(INT))
    elif isinstance(t, TMap):
        e = EMakeMap2(
            EEmptyList().with_type(TBag(t.k)),
            ELambda(EVar("x").with_type(t.k), construct_value(t.v)))
    else:
        h = extension_handler(type(t))
        if h is not None:
            return h.default_value(t)
        raise NotImplementedError(pprint(t))
    return e.with_type(t)

def _uneval(t, value):
    if is_numeric(t):
        return ENum(value).with_type(t)
    elif t == BOOL:
        return EBool(value).with_type(t)
    elif is_collection(t):
        e = EEmptyList().with_type(t)
        for x in value:
            e = EBinOp(e, "+", ESingleton(uneval(t.t, x)).with_type(t)).with_type(t)
        return e
    elif isinstance(t, TString):
        return EStr(value).with_type(t)
    elif isinstance(t, TTuple):
        return ETuple(tuple(uneval(tt, x) for (tt, x) in zip(t.ts, value))).with_type(t)
    elif isinstance(t, TRecord):
        return EMakeRecord(tuple((f, uneval(tt, value[f])) for (f, tt) in t.fields)).with_type(t)
    elif isinstance(t, TEnum):
        return EEnumEntry(value).with_type(t)
    elif isinstance(t, THandle):
        return EHandle(ENum(value.address).with_type(INT), uneval(t.value_type, value.value)).with_type(t)
    elif isinstance(t, TNative):
        return ENative(ENum(value[1]).with_type(INT)).with_type(t)
    else:
        raise NotImplementedError(pprint(t))

@typechecked
def uneval(t : Type, value) -> Exp:
    """
    Produce an expression `e` of type `t` such that `eval(e, {}) == value`.
    """
    res = _uneval(t, value)
    assert eval(res, {}) == value
    return res

def _eval_compiled(ops, init_stk=()):
    ops = list(reversed(ops))
    stk = list(init_stk)
    while ops:
        op = ops.pop()
        new_ops = op(stk)
        if new_ops:
            ops.extend(reversed(new_ops))
    return stk[-1]

def push(val):
    def _push(stk):
        stk.append(val)
    return _push

def push_true(stk):
    stk.append(True)

def push_false(stk):
    stk.append(False)

def make_handle(stk):
    value = stk.pop()
    addr = stk.pop()
    stk.append(Handle(addr, value))

def make_singleton_bag(stk):
    stk.append(Bag((stk.pop(),)))

def make_singleton_list(stk):
    stk.append((stk.pop(),))

def withalteredvalue(stk):
    nv = stk.pop()
    h = stk.pop()
    stk.append(Handle(h.address, nv))

def push_null(stk):
    stk.append(None)

def get_handle_value(stk):
    stk.append(stk.pop().value)

def iterable_to_bag(stk):
    stk.append(Bag(stk.pop()))

def iterable_to_list(stk):
    stk.append(tuple(stk.pop()))

def read_map(stk):
    k = stk.pop()
    m = stk.pop()
    stk.append(m[k])

def has_key(key_type):
    def _has_key(stk):
        k = stk.pop()
        m = stk.pop()
        stk.append(any(eq(key_type, k, kk) for kk in m.keys()))
    return _has_key

def read_map_keys(stk):
    stk.append(Bag(stk.pop().keys()))

def binaryop_add_numbers(stk):
    v2 = stk.pop()
    v1 = stk.pop()
    stk.append(v1 + v2)

def binaryop_add_collections(stk):
    v2 = stk.pop()
    v1 = stk.pop()
    stk.append(Bag(itertools.chain(v1, v2)))

def binaryop_mul(stk):
    v2 = stk.pop()
    v1 = stk.pop()
    stk.append(v1 * v2)

def binaryop_sub(stk):
    v2 = stk.pop()
    v1 = stk.pop()
    stk.append(v1 - v2)

def binaryop_sub_bags(elem_type):
    def binaryop_sub_bags(stk):
        v2 = stk.pop()
        v1 = stk.pop()
        elems = list(v1)
        for x in v2:
            for i in range(len(elems)):
                if eq(elem_type, x, elems[i]):
                    del elems[i]
                    break
        stk.append(Bag(elems))
    return binaryop_sub_bags

def binaryop_sub_lists(elem_type):
    def binaryop_sub_lists(stk):
        v2 = stk.pop()
        v1 = stk.pop()
        elems = list(v1)
        for x in v2:
            for i in range(len(elems)):
                if eq(elem_type, x, elems[i]):
                    del elems[i]
                    break
        stk.append(tuple(elems))
    return binaryop_sub_lists

def binaryop_eq(t, deep=False):
    def binaryop_eq(stk):
        v2 = stk.pop()
        v1 = stk.pop()
        stk.append(cmp(t, v1, v2, deep=deep) == EQ)
    return binaryop_eq

def binaryop_ne(t):
    def binaryop_ne(stk):
        v2 = stk.pop()
        v1 = stk.pop()
        stk.append(cmp(t, v1, v2) != EQ)
    return binaryop_ne

def binaryop_lt(t):
    def binaryop_lt(stk):
        v2 = stk.pop()
        v1 = stk.pop()
        stk.append(cmp(t, v1, v2) == LT)
    return binaryop_lt

def binaryop_le(t):
    def binaryop_le(stk):
        v2 = stk.pop()
        v1 = stk.pop()
        stk.append(cmp(t, v1, v2) != GT)
    return binaryop_le

def binaryop_gt(t):
    def binaryop_gt(stk):
        v2 = stk.pop()
        v1 = stk.pop()
        stk.append(cmp(t, v1, v2) == GT)
    return binaryop_gt

def binaryop_ge(t):
    def binaryop_ge(stk):
        v2 = stk.pop()
        v1 = stk.pop()
        stk.append(cmp(t, v1, v2) != LT)
    return binaryop_ge

def binaryop_in(elem_type):
    def binaryop_in(stk):
        v2 = stk.pop()
        v1 = stk.pop()
        stk.append(any(eq(elem_type, v1, v2elem) for v2elem in v2))
    return binaryop_in

def unaryop_not(stk):
    stk.append(not stk.pop())

def unaryop_sum(stk):
    stk.append(sum(stk.pop()))

def unaryop_all(stk):
    stk.append(all(stk.pop()))

def unaryop_any(stk):
    stk.append(any(stk.pop()))

def unaryop_exists(stk):
    stk.append(bool(stk.pop()))

def unaryop_empty(stk):
    stk.append(not stk.pop())

def unaryop_neg(stk):
    stk.append(-stk.pop())

def unaryop_areunique(elem_type):
    keyfunc = cmp_to_key(lambda v1, v2: cmp(elem_type, v1, v2))
    def unaryop_areunique(stk):
        v = stk.pop()
        l = sorted(v, key=keyfunc)
        res = True
        for i in range(len(l) - 1):
            if eq(elem_type, l[i], l[i+1]):
                res = False
                break
        stk.append(res)
    return unaryop_areunique

def unaryop_distinct(elem_type):
    def unaryop_distinct(stk):
        v = stk.pop()
        res = []
        for x in v:
            if not any(eq(elem_type, x, y) for y in res):
                res.append(x)
        stk.append(Bag(res))
    return unaryop_distinct

def unaryop_the(default):
    def _unaryop_the(stk):
        v = stk.pop()
        stk.append(v[0] if v else default)
    return _unaryop_the

def unaryop_reversed(stk):
    stk.append(tuple(reversed(stk.pop())))

def unaryop_len(stk):
    stk.append(len(stk.pop()))

def do_concat(stk):
    v = stk.pop()
    stk.append(Bag(elem for bag in v for elem in bag))

def if_then_else(then_code, else_code):
    def ite(stk):
        return then_code if stk.pop() else else_code
    return ite

def dup(stk):
    stk.append(stk[-1])

def swp(stk):
    x = stk.pop()
    y = stk.pop()
    stk.append(x)
    stk.append(y)

def drop(stk):
    stk.pop()

def drop_front(stk):
    l = stk.pop()
    stk.append(l[1:])

def drop_back(stk):
    l = stk.pop()
    stk.append(l[:-1])

def list_index(default):
    def _list_index(stk):
        i = stk.pop()
        l = stk.pop()
        stk.append(
            l[i] if i >= 0 and i < len(l) else
            default)
    return _list_index

def list_slice(stk):
    end   = max(stk.pop(), 0)
    start = max(stk.pop(), 0)
    l = stk.pop()
    stk.append(l[start:end])

_EMPTY_BAG = Bag()
def _compile(e, env : {str:int}, out, bind_callback):
    if isinstance(e, EVar):
        i = env[e.id]
        if isinstance(i, int):
            def load_var(stk):
                stk.append(stk[i])
            out.append(load_var)
        else:
            def load_bound(stk):
                stk.append(i())
            out.append(load_bound)
    elif isinstance(e, EBool):
        out.append(push_true if e.val else push_false)
    elif isinstance(e, ENum):
        s = e.val
        def push_num(stk):
            stk.append(s)
        out.append(push_num)
    elif isinstance(e, EStr):
        s = e.val
        def push_str(stk):
            stk.append(s)
        out.append(push_str)
    elif isinstance(e, EEnumEntry):
        s = e.name
        def push_enum(stk):
            stk.append(s)
        out.append(push_enum)
    elif isinstance(e, EEmptyList):
        def push_empty_list(stk):
            stk.append(_EMPTY_BAG)
        out.append(push_empty_list)
    elif isinstance(e, ESingleton):
        _compile(e.e, env, out, bind_callback=bind_callback)
        if isinstance(e.type, TList):
            out.append(make_singleton_list)
        else:
            out.append(make_singleton_bag)
    elif isinstance(e, EHandle):
        _compile(e.addr, env, out, bind_callback=bind_callback)
        _compile(e.value, env, out, bind_callback=bind_callback)
        out.append(make_handle)
    elif isinstance(e, EWithAlteredValue):
        _compile(e.handle, env, out, bind_callback=bind_callback)
        _compile(e.new_value, env, out, bind_callback=bind_callback)
        out.append(withalteredvalue)
    elif isinstance(e, ENull):
        out.append(push_null)
    elif isinstance(e, ECond):
        _compile(e.cond, env, out, bind_callback=bind_callback)
        then_code = []; _compile(e.then_branch, env, then_code, bind_callback=bind_callback)
        else_code = []; _compile(e.else_branch, env, else_code, bind_callback=bind_callback)
        def ite(stk):
            return then_code if stk.pop() else else_code
        out.append(ite)
    elif isinstance(e, EMakeRecord):
        for (f, ee) in e.fields:
            _compile(ee, env, out, bind_callback=bind_callback)
        def make_record(stk):
            stk.append(FrozenDict((f, stk.pop()) for (f, _) in reversed(e.fields)))
        out.append(make_record)
    elif isinstance(e, EGetField):
        _compile(e.e, env, out, bind_callback=bind_callback)
        if isinstance(e.e.type, THandle):
            assert e.f == "val"
            out.append(get_handle_value)
        else:
            assert isinstance(e.e.type, TRecord)
            f = e.f
            def get_field(stk):
                stk.append(stk.pop()[f])
            out.append(get_field)
    elif isinstance(e, ETuple):
        n = len(e.es)
        for ee in e.es:
            _compile(ee, env, out, bind_callback=bind_callback)
        def make_tuple(stk):
            entries = reversed([stk.pop() for i in range(n)])
            stk.append(tuple(entries))
        out.append(make_tuple)
    elif isinstance(e, ETupleGet):
        _compile(e.e, env, out, bind_callback=bind_callback)
        def tuple_get(stk):
            stk.append(stk.pop()[e.n])
        out.append(tuple_get)
    elif isinstance(e, EStateVar):
        _compile(e.e, env, out, bind_callback=bind_callback)
    elif isinstance(e, ENative):
        _compile(e.e, env, out, bind_callback=bind_callback)
        def make_native(stk):
            stk.append((e.type.name, stk.pop()))
        out.append(make_native)
    elif isinstance(e, EUnaryOp):
        _compile(e.e, env, out, bind_callback=bind_callback)
        if e.op == UOp.Not:
            out.append(unaryop_not)
        elif e.op == UOp.Sum:
            out.append(unaryop_sum)
        elif e.op == UOp.Exists:
            out.append(unaryop_exists)
        elif e.op == UOp.Empty:
            out.append(unaryop_empty)
        elif e.op == UOp.All:
            out.append(unaryop_all)
        elif e.op == UOp.Any:
            out.append(unaryop_any)
        elif e.op == UOp.Length:
            out.append(unaryop_len)
        elif e.op == UOp.AreUnique:
            out.append(unaryop_areunique(e.e.type.t))
        elif e.op == UOp.Distinct:
            out.append(unaryop_distinct(e.e.type.t))
        elif e.op == UOp.The:
            out.append(unaryop_the(default=mkval(e.type)))
        elif e.op == UOp.Reversed:
            out.append(unaryop_reversed)
        elif e.op == "-":
            out.append(unaryop_neg)
        else:
            raise NotImplementedError(e.op)
    elif isinstance(e, EBinOp):
        if e.op == "and":
            return _compile(ECond(e.e1, e.e2, F).with_type(BOOL), env, out, bind_callback=bind_callback)
        elif e.op == "or":
            return _compile(ECond(e.e1, T, e.e2).with_type(BOOL), env, out, bind_callback=bind_callback)
        _compile(e.e1, env, out, bind_callback=bind_callback)
        _compile(e.e2, env, out, bind_callback=bind_callback)
        e1type = e.e1.type
        if e.op == "+":
            if is_collection(e.type):
                out.append(binaryop_add_collections)
            else:
                out.append(binaryop_add_numbers)
        elif e.op == "*":
            out.append(binaryop_mul)
        elif e.op == "-":
            if isinstance(e.type, TBag) or isinstance(e.type, TSet):
                out.append(binaryop_sub_bags(e.type.t))
            elif isinstance(e.type, TList):
                out.append(binaryop_sub_lists(e.type.t))
            else:
                out.append(binaryop_sub)
        elif e.op == "==":
            out.append(binaryop_eq(e1type))
        elif e.op == "===":
            out.append(binaryop_eq(e1type, deep=True))
        elif e.op == "<":
            out.append(binaryop_lt(e1type))
        elif e.op == ">":
            out.append(binaryop_gt(e1type))
        elif e.op == "<=":
            out.append(binaryop_le(e1type))
        elif e.op == ">=":
            out.append(binaryop_ge(e1type))
        elif e.op == "!=":
            out.append(binaryop_ne(e1type))
        elif e.op == BOp.In:
            out.append(binaryop_in(e1type))
        else:
            raise NotImplementedError(e.op)
    elif isinstance(e, EListGet):
        _compile(e.e, env, out, bind_callback=bind_callback)
        _compile(e.index, env, out, bind_callback=bind_callback)
        out.append(list_index(mkval(e.type)))
    elif isinstance(e, EListSlice):
        _compile(e.e, env, out, bind_callback=bind_callback)
        _compile(e.start, env, out, bind_callback=bind_callback)
        _compile(e.end, env, out, bind_callback=bind_callback)
        out.append(list_slice)
    elif isinstance(e, EDropFront):
        _compile(e.e, env, out, bind_callback=bind_callback)
        out.append(drop_front)
    elif isinstance(e, EDropBack):
        _compile(e.e, env, out, bind_callback=bind_callback)
        out.append(drop_back)
    elif isinstance(e, EFilter):
        _compile(e.e, env, out, bind_callback=bind_callback)
        box = [None]
        body = []
        with extend(env, e.p.arg.id, lambda: box[0]):
            _compile(e.p.body, env, body, bind_callback=bind_callback)
        def set_arg(v):
            def set_arg(stk):
                box[0] = v
            return set_arg
        def maybe_append_to_result(idx):
            return lambda stk: (stk[idx].append(box[0]) if stk.pop() else None)
        def do_filter(stk):
            bag = stk.pop()
            res_idx = len(stk)
            stk.append([])
            ops = []
            for (i, val) in enumerate(bag):
                ops.append(set_arg(val))
                bind_callback(e.p.arg, val)
                ops.extend(body)
                ops.append(maybe_append_to_result(res_idx))
            return ops
        out.append(do_filter)
        out.append(iterable_to_bag)
    elif isinstance(e, EMap):
        _compile(e.e, env, out, bind_callback=bind_callback)
        box = [None]
        body = []
        with extend(env, e.f.arg.id, lambda: box[0]):
            _compile(e.f.body, env, body, bind_callback=bind_callback)
        def set_arg(v):
            def set_arg(stk):
                box[0] = v
            return set_arg
        def append_to_result(idx):
            return lambda stk: stk[idx].append(stk.pop())
        def do_map(stk):
            bag = stk.pop()
            res_idx = len(stk)
            stk.append([])
            ops = []
            for (i, val) in enumerate(bag):
                ops.append(set_arg(val))
                bind_callback(e.f.arg, val)
                ops.extend(body)
                ops.append(append_to_result(res_idx))
            return ops
        out.append(do_map)
        out.append(iterable_to_bag)
    elif isinstance(e, EFlatMap):
        _compile(EMap(e.e, e.f).with_type(TBag(e.type)), env, out, bind_callback=bind_callback)
        out.append(do_concat)
    elif isinstance(e, EArgMin) or isinstance(e, EArgMax):
        # stack layout:
        #   len | f(best) | best | elem_0 | ... | elem_len

        # body is a seq. of opcodes that has the effect of pushing
        # f(top_of_stack) onto the stack, leaving the old top underneath
        box = [None]
        def set_arg(stk):
            box[0] = stk[-1]
        body = [set_arg]
        with extend(env, e.f.arg.id, lambda: box[0]):
            _compile(e.f.body, env, body, bind_callback=bind_callback)

        keytype = e.f.body.type

        def initialize(stk):
            bag = stk.pop()
            if bag:
                stk.extend(reversed(bag))
            else:
                stk.append(mkval(e.type))
            return body + [push(len(bag)-1)]

        do_cmp = binaryop_lt(keytype) if isinstance(e, EArgMin) else binaryop_gt(keytype)
        def loop(stk):
            len = stk.pop()
            key = stk.pop()
            if len > 0:
                best = stk.pop()
                return body + [dup, push(key), do_cmp, if_then_else(
                    [],
                    [drop, drop, push(best), push(key)]), push(len-1), loop]

        _compile(e.e, env, out, bind_callback=bind_callback)
        out.append(initialize)
        out.append(loop)
    elif isinstance(e, EMakeMap2):
        _compile(EMap(e.e, ELambda(e.value.arg, ETuple((e.value.arg, e.value.body)).with_type(TTuple((e.value.arg.type, e.value.body.type))))).with_type(TBag(TTuple((e.value.arg.type, e.value.body.type)))), env, out, bind_callback=bind_callback)
        default = mkval(e.type.v)
        def make_map(stk):
            res = Map(e.type, default)
            for (k, v) in reversed(list(stk.pop())):
                res[k] = v
            stk.append(res)
        out.append(make_map)
    elif isinstance(e, EMapGet):
        _compile(e.map, env, out, bind_callback=bind_callback)
        _compile(e.key, env, out, bind_callback=bind_callback)
        out.append(read_map)
    elif isinstance(e, EHasKey):
        _compile(e.map, env, out, bind_callback=bind_callback)
        _compile(e.key, env, out, bind_callback=bind_callback)
        out.append(has_key(e.key.type))
    elif isinstance(e, EMapKeys):
        _compile(e.e, env, out, bind_callback=bind_callback)
        out.append(read_map_keys)
    elif isinstance(e, ECall):
        _compile(EVar(e.func), env, out, bind_callback=bind_callback)
        for a in e.args:
            _compile(a, env, out, bind_callback=bind_callback)
        n = len(e.args)
        def call(stk):
            args = reversed([stk.pop() for i in range(n)])
            f = stk.pop()
            stk.append(f(*args))
        out.append(call)
    elif isinstance(e, ELet):
        _compile(e.e, env, out, bind_callback=bind_callback)
        box = [None]
        def set_arg(v):
            def set_arg(stk):
                box[0] = v
            return set_arg
        def do_bind(stk):
            return [set_arg(stk.pop())]
        out.append(do_bind)
        with extend(env, e.f.arg.id, lambda: box[0]):
            _compile(e.f.body, env, out, bind_callback=bind_callback)
    else:
        h = extension_handler(type(e))
        if h is not None:
            _compile(h.encode(e), env, out, bind_callback=bind_callback)
        else:
            raise NotImplementedError(type(e))
    if hasattr(e, "type") and isinstance(e.type, TList):
        out.append(iterable_to_list)

def free_vars_and_funcs(e):
    for v in free_vars(e):
        yield v.id
    for f in free_funcs(e):
        yield f

def eval_bulk(e, envs, bind_callback=None, use_default_values_for_undefined_vars : bool = False):
    e = purify(e)
    if bind_callback is None:
        bind_callback = lambda arg, val: None
    # return [eval(e, env, bind_callback=bind_callback) for env in envs]
    if not envs:
        return []
    ops = []
    vars = OrderedSet(free_vars_and_funcs(e))
    types = { v.id : v.type for v in free_vars(e) }
    vmap = { v : i for (i, v) in enumerate(vars) }
    try:
        envs = [ [(env.get(v, mkval(types[v])) if (use_default_values_for_undefined_vars and v in types) else env[v]) for v in vars] for env in envs ]
    except KeyError:
        import sys
        print("OH NO", file=sys.stderr)
        print("e = {}".format(pprint(e)), file=sys.stderr)
        print("eval_bulk({!r}, {!r}, use_default_values_for_undefined_vars={!r})".format(e, envs, use_default_values_for_undefined_vars), file=sys.stderr)
        # import pdb
        # pdb.set_trace()
        raise
    _compile(e, vmap, ops, bind_callback)
    return [_eval_compiled(ops, env) for env in envs]
