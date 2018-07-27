"""Interpreter for Cozy expressions.

Important functions:
 - eval: execute an expression in an environment
 - eval_bulk: execute the same expression in many different environments
"""

from functools import cmp_to_key, lru_cache
import itertools
from fractions import Fraction

from cozy.target_syntax import *
from cozy.syntax_tools import pprint, free_vars, free_vars_and_funcs, purify
from cozy.common import FrozenDict, OrderedSet, extend, unique
from cozy.typecheck import is_numeric, is_collection
from cozy.structures import extension_handler
from cozy.value_types import Map, Bag, Handle, compare_values, values_equal, LT, EQ, GT

def eval(e : Exp, env : {str:object}, *args, **kwargs):
    """Evaluate an expression in an environment.

    Parameters:
        e - a Cozy expression
        env - an environment mapping variable names to values
        use_default_values_for_undefined_vars - boolean indicating whether to
            use a default value for any variable missing in the environment.
            If false, then an error is thrown when a variable has no associated
            value. Defaults to False.
    """
    return eval_bulk(e, (env,), *args, **kwargs)[0]

def eval_bulk(
        e : Exp,
        envs : [{str:object}],
        use_default_values_for_undefined_vars : bool = False):
    """Evaluate an expression in many different environments.

    This function accepts the same arguments as `eval`, but takes a list of
    environments instead of just one.

    The call

        eval_bulk(e, envs)

    is equivalent to

        [eval(e, env) for env in envs].

    However, using `eval_bulk` is much faster than repeatedly calling `eval` on
    the same expression.
    """

    e = purify(e)
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
        raise
    _compile(e, vmap, ops)
    return [_eval_compiled(ops, env) for env in envs]

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
        e = EFALSE
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
            return h.default_value(t, construct_value)
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
            e = EBinOp(e, "+", ESingleton(uneval(t.elem_type, x)).with_type(t)).with_type(t)
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
        stk.append(any(values_equal(key_type, k, kk) for kk in m.keys()))
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

def binaryop_add_sets(stk):
    v2 = stk.pop()
    v1 = stk.pop()
    stk.append(Bag(unique(itertools.chain(v1, v2))))

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
                if values_equal(elem_type, x, elems[i]):
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
                if values_equal(elem_type, x, elems[i]):
                    del elems[i]
                    break
        stk.append(tuple(elems))
    return binaryop_sub_lists

def binaryop_eq(t, deep=False):
    def binaryop_eq(stk):
        v2 = stk.pop()
        v1 = stk.pop()
        stk.append(compare_values(t, v1, v2, deep=deep) == EQ)
    return binaryop_eq

def binaryop_ne(t):
    def binaryop_ne(stk):
        v2 = stk.pop()
        v1 = stk.pop()
        stk.append(compare_values(t, v1, v2) != EQ)
    return binaryop_ne

def binaryop_lt(t):
    def binaryop_lt(stk):
        v2 = stk.pop()
        v1 = stk.pop()
        stk.append(compare_values(t, v1, v2) == LT)
    return binaryop_lt

def binaryop_le(t):
    def binaryop_le(stk):
        v2 = stk.pop()
        v1 = stk.pop()
        stk.append(compare_values(t, v1, v2) != GT)
    return binaryop_le

def binaryop_gt(t):
    def binaryop_gt(stk):
        v2 = stk.pop()
        v1 = stk.pop()
        stk.append(compare_values(t, v1, v2) == GT)
    return binaryop_gt

def binaryop_ge(t):
    def binaryop_ge(stk):
        v2 = stk.pop()
        v1 = stk.pop()
        stk.append(compare_values(t, v1, v2) != LT)
    return binaryop_ge

def binaryop_in(elem_type):
    def binaryop_in(stk):
        v2 = stk.pop()
        v1 = stk.pop()
        stk.append(any(values_equal(elem_type, v1, v2elem) for v2elem in v2))
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
    keyfunc = cmp_to_key(lambda v1, v2: compare_values(elem_type, v1, v2))
    def unaryop_areunique(stk):
        v = stk.pop()
        l = sorted(v, key=keyfunc)
        res = True
        for i in range(len(l) - 1):
            if values_equal(elem_type, l[i], l[i+1]):
                res = False
                break
        stk.append(res)
    return unaryop_areunique

def unaryop_distinct(elem_type):
    def unaryop_distinct(stk):
        v = stk.pop()
        res = []
        for x in v:
            if not any(values_equal(elem_type, x, y) for y in res):
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
def _compile(e, env : {str:int}, out):
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
        if e.type == FLOAT:
            s = Fraction(s)
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
        _compile(e.e, env, out)
        if isinstance(e.type, TList):
            out.append(make_singleton_list)
        else:
            out.append(make_singleton_bag)
    elif isinstance(e, EHandle):
        _compile(e.addr, env, out)
        _compile(e.value, env, out)
        out.append(make_handle)
    elif isinstance(e, ENull):
        out.append(push_null)
    elif isinstance(e, ECond):
        _compile(e.cond, env, out)
        then_code = []; _compile(e.then_branch, env, then_code)
        else_code = []; _compile(e.else_branch, env, else_code)
        def ite(stk):
            return then_code if stk.pop() else else_code
        out.append(ite)
    elif isinstance(e, EMakeRecord):
        for (f, ee) in e.fields:
            _compile(ee, env, out)
        def make_record(stk):
            stk.append(FrozenDict((f, stk.pop()) for (f, _) in reversed(e.fields)))
        out.append(make_record)
    elif isinstance(e, EGetField):
        _compile(e.e, env, out)
        if isinstance(e.e.type, THandle):
            assert e.field_name == "val"
            out.append(get_handle_value)
        else:
            assert isinstance(e.e.type, TRecord)
            f = e.field_name
            def get_field(stk):
                stk.append(stk.pop()[f])
            out.append(get_field)
    elif isinstance(e, ETuple):
        n = len(e.es)
        for ee in e.es:
            _compile(ee, env, out)
        def make_tuple(stk):
            entries = reversed([stk.pop() for i in range(n)])
            stk.append(tuple(entries))
        out.append(make_tuple)
    elif isinstance(e, ETupleGet):
        _compile(e.e, env, out)
        def tuple_get(stk):
            stk.append(stk.pop()[e.index])
        out.append(tuple_get)
    elif isinstance(e, EStateVar):
        _compile(e.e, env, out)
    elif isinstance(e, ENative):
        _compile(e.e, env, out)
        def make_native(stk):
            stk.append((e.type.name, stk.pop()))
        out.append(make_native)
    elif isinstance(e, EUnaryOp):
        _compile(e.e, env, out)
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
            out.append(unaryop_areunique(e.e.type.elem_type))
        elif e.op == UOp.Distinct:
            out.append(unaryop_distinct(e.e.type.elem_type))
        elif e.op == UOp.The:
            out.append(unaryop_the(default=mkval(e.type)))
        elif e.op == UOp.Reversed:
            out.append(unaryop_reversed)
        elif e.op == "-":
            out.append(unaryop_neg)
        else:
            raise NotImplementedError(e.op)
    elif isinstance(e, EBinOp):
        if e.op == BOp.And:
            return _compile(ECond(e.e1, e.e2, EFALSE).with_type(BOOL), env, out)
        elif e.op == BOp.Or:
            return _compile(ECond(e.e1, ETRUE, e.e2).with_type(BOOL), env, out)
        elif e.op == "=>":
            return _compile(ECond(e.e1, e.e2, ETRUE).with_type(BOOL), env, out)
        _compile(e.e1, env, out)
        _compile(e.e2, env, out)
        e1type = e.e1.type
        if e.op == "+":
            if is_collection(e.type):
                out.append(binaryop_add_sets if isinstance(e.type, TSet) else binaryop_add_collections)
            else:
                out.append(binaryop_add_numbers)
        elif e.op == "*":
            out.append(binaryop_mul)
        elif e.op == "-":
            if isinstance(e.type, TBag) or isinstance(e.type, TSet):
                out.append(binaryop_sub_bags(e.type.elem_type))
            elif isinstance(e.type, TList):
                out.append(binaryop_sub_lists(e.type.elem_type))
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
        _compile(e.e, env, out)
        _compile(e.index, env, out)
        out.append(list_index(mkval(e.type)))
    elif isinstance(e, EListSlice):
        _compile(e.e, env, out)
        _compile(e.start, env, out)
        _compile(e.end, env, out)
        out.append(list_slice)
    elif isinstance(e, EDropFront):
        _compile(e.e, env, out)
        out.append(drop_front)
    elif isinstance(e, EDropBack):
        _compile(e.e, env, out)
        out.append(drop_back)
    elif isinstance(e, EFilter):
        _compile(e.e, env, out)
        box = [None]
        body = []
        with extend(env, e.p.arg.id, lambda: box[0]):
            _compile(e.p.body, env, body)
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
                ops.extend(body)
                ops.append(maybe_append_to_result(res_idx))
            return ops
        out.append(do_filter)
        out.append(iterable_to_bag)
    elif isinstance(e, EMap):
        _compile(e.e, env, out)
        box = [None]
        body = []
        with extend(env, e.key_function.arg.id, lambda: box[0]):
            _compile(e.key_function.body, env, body)
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
                ops.extend(body)
                ops.append(append_to_result(res_idx))
            return ops
        out.append(do_map)
        out.append(iterable_to_bag)
    elif isinstance(e, EFlatMap):
        _compile(EMap(e.e, e.key_function).with_type(TBag(e.type)), env, out)
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
        with extend(env, e.key_function.arg.id, lambda: box[0]):
            _compile(e.key_function.body, env, body)

        keytype = e.key_function.body.type

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

        _compile(e.e, env, out)
        out.append(initialize)
        out.append(loop)
    elif isinstance(e, EMakeMap2):
        _compile(EMap(e.e, ELambda(e.value.arg, ETuple((e.value.arg, e.value.body)).with_type(TTuple((e.value.arg.type, e.value.body.type))))).with_type(TBag(TTuple((e.value.arg.type, e.value.body.type)))), env, out)
        default = mkval(e.type.v)
        def make_map(stk):
            res = Map(e.type, default)
            for (k, v) in reversed(list(stk.pop())):
                res[k] = v
            stk.append(res)
        out.append(make_map)
    elif isinstance(e, EMapGet):
        _compile(e.map, env, out)
        _compile(e.key, env, out)
        out.append(read_map)
    elif isinstance(e, EHasKey):
        _compile(e.map, env, out)
        _compile(e.key, env, out)
        out.append(has_key(e.key.type))
    elif isinstance(e, EMapKeys):
        _compile(e.e, env, out)
        out.append(read_map_keys)
    elif isinstance(e, ECall):
        _compile(EVar(e.func), env, out)
        for a in e.args:
            _compile(a, env, out)
        n = len(e.args)
        def call(stk):
            args = reversed([stk.pop() for i in range(n)])
            f = stk.pop()
            stk.append(f(*args))
        out.append(call)
    elif isinstance(e, ELet):
        _compile(e.e, env, out)
        box = [None]
        def set_arg(v):
            def set_arg(stk):
                box[0] = v
            return set_arg
        def do_bind(stk):
            return [set_arg(stk.pop())]
        out.append(do_bind)
        with extend(env, e.f.arg.id, lambda: box[0]):
            _compile(e.f.body, env, out)
    else:
        h = extension_handler(type(e))
        if h is not None:
            _compile(h.encode(e), env, out)
        else:
            raise NotImplementedError(type(e))
    if hasattr(e, "type") and isinstance(e.type, TList):
        out.append(iterable_to_list)
