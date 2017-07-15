from collections import UserDict, defaultdict, namedtuple
from functools import total_ordering

from cozy.target_syntax import *
from cozy.syntax_tools import equal, pprint
from cozy.common import Visitor, FrozenDict, unique, extend
from cozy.typecheck import is_numeric

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
        for (k, v) in self._items:
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
class Maybe(object):
    def __init__(self, obj):
        self.obj = obj
    def __hash__(self):
        return hash(self.obj)
    def __eq__(self, other):
        return ((self.obj is None) == (other.obj is None)) and self.obj == other.obj
    def __lt__(self, other):
        if self.obj is None and other.obj is not None:
            return True
        elif self.obj is not None and other.obj is None:
            return False
        elif self.obj is None and other.obj is None:
            return False
        else:
            return self.obj < other.obj

@total_ordering
class Bag(object):
    def __init__(self, iterable=()):
        self.elems = tuple(iterable)
    def __hash__(self):
        return hash(tuple(sorted(self.elems)))
    def __add__(self, other):
        return Bag(self.elems + other.elems)
    def __eq__(self, other):
        return sorted(self.elems) == sorted(other.elems)
    def __lt__(self, other):
        return sorted(self.elems) < sorted(other.elems)
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
def cmp(t, v1, v2):
    stk = [(t, v1, v2)]
    while stk:
        (t, v1, v2) = stk[-1]
        del stk[-1]

        if isinstance(t, THandle):
            if v1.address == v2.address: continue
            if v1.address <  v2.address: return LT
            else:                        return GT
        elif isinstance(t, TEnum):
            i1 = t.cases.index(v1)
            i2 = t.cases.index(v2)
            if i1 == i2: continue
            if i1 <  i2: return LT
            else:        return GT
        elif isinstance(t, TBag) or isinstance(t, TSet):
            elems1 = list(sorted(v1))
            elems2 = list(sorted(v2))
            if len(elems1) < len(elems2): return LT
            if len(elems1) > len(elems2): return GT
            stk.extend(reversed([(t.t, x, y) for (x, y) in zip(elems1, elems2)]))
        elif isinstance(t, TMap):
            keys1 = Bag(sorted(v1.keys()))
            keys2 = Bag(v2.keys())
            stk.extend(reversed([(t.v, v1[k], v2[k]) for k in keys1]))
            stk.append((TSet(t.k), keys1, keys2))
            stk.append((t.v, v1.default, v2.default))
        elif isinstance(t, TMaybe):
            if v1.obj is None and v2.obj is None:
                continue
            elif v1.obj is None:
                return LT
            elif v2.obj is None:
                return GT
            stk.append((t.t, v1.obj, v2.obj))
        elif isinstance(t, TTuple):
            stk.extend(reversed([(tt, vv1, vv2) for (tt, vv1, vv2) in zip(t.ts, v1, v2)]))
        elif isinstance(t, TRecord):
            stk.extend(reversed([(ft, v1[f], v2[f]) for (f, ft) in t.fields]))
        else:
            if   v1 == v2: continue
            elif v1 <  v2: return LT
            else:          return GT
    return EQ

def eq(t, v1, v2):
    return cmp(t, v1, v2) == EQ

class Evaluator(Visitor):
    def __init__(self, bind_callback):
        self.bind_callback = bind_callback
    def visit_EVar(self, v, env):
        return env[v.id]
    def visit_ENum(self, n, env):
        return n.val
    def visit_EBool(self, b, env):
        return b.val
    def visit_EHandle(self, e, env):
        return Handle(self.visit(e.addr, env), self.visit(e.value, env))
    def visit_EStr(self, e, env):
        return e.val
    def visit_EEmptyList(self, e, env):
        return Bag()
    def visit_ESingleton(self, e, env):
        return Bag((self.visit(e.e, env),))
    def visit_EJust(self, e, env):
        return Maybe(self.visit(e.e, env))
    def visit_ENull(self, e, env):
        return Maybe(None)
    def visit_ECall(self, call, env):
        return env[call.func](*[self.visit(arg, env) for arg in call.args])
    def visit_ELet(self, e, env):
        return self.eval_lambda(e.f, self.visit(e.e, env), env)
    def visit_ECond(self, e, env):
        if self.visit(e.cond, env):
            return self.visit(e.then_branch, env)
        else:
            return self.visit(e.else_branch, env)
    def visit_EEnumEntry(self, val, env):
        # return val.type.cases.index(val.name)
        return val.name
    def visit_ENative(self, val, env):
        return (val.type.name, self.visit(val.e, env))
    def visit_EWithAlteredValue(self, e, env):
        h = self.visit(e.handle, env)
        new_val = self.visit(e.new_value, env)
        return Handle(h.address, new_val)
    def visit_EGetField(self, e, env):
        lhs = self.visit(e.e, env)
        if isinstance(e.e.type, THandle):
            assert e.f == "val"
            return lhs.value
        return lhs[e.f]
    def visit_EUnaryOp(self, e, env):
        if e.op == UOp.Not:
            return not self.visit(e.e, env)
        elif e.op == UOp.Sum:
            return sum(self.visit(e.e, env))
        elif e.op == UOp.Exists:
            return bool(self.visit(e.e, env))
        elif e.op == UOp.Empty:
            return not bool(self.visit(e.e, env))
        elif e.op == UOp.AreUnique:
            l = sorted(self.visit(e.e, env))
            for i in range(len(l) - 1):
                if eq(e.e.type.t, l[i], l[i+1]):
                    return False
            return True
        elif e.op == UOp.Distinct:
            res = []
            for x in sorted(self.visit(e.e, env)):
                if not res or not eq(e.e.type.t, res[-1], x):
                    res.append(x)
            return Bag(res)
        elif e.op == UOp.The:
            bag = self.visit(e.e, env)
            if bag:
                return Maybe(bag[0])
            else:
                return self.visit(ENull().with_type(e.type), env)
        elif e.op == "-":
            return -self.visit(e.e, env)
        else:
            raise NotImplementedError(e.op)
    def visit_EBinOp(self, e, env):
        # short-circuit operators
        if e.op == BOp.And:
            return self.visit(e.e1, env) and self.visit(e.e2, env)
        elif e.op == BOp.Or:
            return self.visit(e.e1, env) or self.visit(e.e2, env)

        v1 = self.visit(e.e1, env)
        v2 = self.visit(e.e2, env)
        e1type = e.e1.type
        if e.op == "+":
            return v1 + v2
        elif e.op == "-":
            if isinstance(e1type, TBag):
                elems = list(v1)
                for x in v2:
                    for i in range(len(elems)):
                        if eq(e1type.t, x, elems[i]):
                            del elems[i]
                            break
                return Bag(elems)
            return v1 - v2
        elif e.op == "==":
            return cmp(e1type, v1, v2) == EQ
        elif e.op == "<":
            return cmp(e1type, v1, v2) == LT
        elif e.op == ">":
            return cmp(e1type, v1, v2) == GT
        elif e.op == "<=":
            return cmp(e1type, v1, v2) != GT
        elif e.op == ">=":
            return cmp(e1type, v1, v2) != LT
        elif e.op == "!=":
            return cmp(e1type, v1, v2) != EQ
        elif e.op == BOp.In:
            return any(eq(e1type, v1, v2elem) for v2elem in v2)
        else:
            raise NotImplementedError(e.op)
    def visit_ETuple(self, e, env):
        return tuple(self.visit(ee, env) for ee in e.es)
    def visit_ETupleGet(self, e, env):
        tup = self.visit(e.e, env)
        return tup[e.n]
    def visit_EApp(self, e, env):
        return self.eval_lambda(e.f, self.visit(e.arg, env), env)
    def visit_EListComprehension(self, e, env):
        return Bag(self.visit_clauses(e.clauses, e.e, env))
    def eval_lambda(self, lam, arg, env):
        self.bind_callback(lam.arg, arg)
        with extend(env, lam.arg.id, arg):
            return self.visit(lam.body, env)
    def visit_EAlterMaybe(self, e, env):
        x = self.visit(e.e, env)
        if x.obj is not None:
            x = Maybe(self.eval_lambda(e.f, x.obj, env))
        return x
    def visit_EMakeRecord(self, e, env):
        return FrozenDict({ f:self.visit(v, env) for (f, v) in e.fields })
    def visit_EMakeMap(self, e, env):
        default = self.eval_lambda(e.value, Bag(), env)
        im = Map(TMap(e.type.k, e.e.type), Bag())
        for x in self.visit(e.e, env):
            im[self.eval_lambda(e.key, x, env)] += Bag((x,))
        res = Map(e.type, default)
        for (k, es) in im.items():
            res[k] = self.eval_lambda(e.value, es, env)
        return res
    def visit_EMakeMap2(self, e, env):
        default = mkval(e.type.v)
        res = Map(e.type, default)
        for x in self.visit(e.e, env):
            res[x] = self.eval_lambda(e.value, x, env)
        return res
    def visit_EMapGet(self, e, env):
        return self.visit(e.map, env)[self.visit(e.key, env)]
    def visit_EMapKeys(self, e, env):
        return Bag(self.visit(e.e, env).keys())
    def visit_EMap(self, e, env):
        return Bag(self.eval_lambda(e.f, x, env) for x in self.visit(e.e, env))
    def visit_EFilter(self, e, env):
        return Bag(x for x in self.visit(e.e, env) if self.eval_lambda(e.p, x, env))
    def visit_EFlatMap(self, e, env):
        res = self.visit(EMap(e.e, e.f).with_type(TBag(e.type.t)), env)
        return Bag(elem for bag in res for elem in bag)
    def visit_clauses(self, clauses, e, env):
        if not clauses:
            yield self.visit(e, env)
            return
        c = clauses[0]
        if isinstance(c, CCond):
            if self.visit(c.e, env):
                yield from self.visit_clauses(clauses[1:], e, env)
        elif isinstance(c, CPull):
            for x in self.visit(c.e, env):
                env2 = dict(env)
                env2[c.id] = x
                yield from self.visit_clauses(clauses[1:], e, env2)
    def visit_EStateVar(self, e, env):
        return self.visit(e.e, env)
    def visit_Exp(self, e, env):
        raise NotImplementedError("eval({})".format(e))
    def visit_object(self, o, *args):
        raise Exception("cannot eval {}".format(repr(o)))

def eval(e, env, bind_callback=lambda arg, val: None):
    return Evaluator(bind_callback).visit(e, env)

def mkval(type : Type):
    """
    Produce an arbitrary value of the given type.
    """
    if isinstance(type, TInt) or isinstance(type, TLong):
        return 0
    if isinstance(type, TNative):
        return (type.name, 0)
    if isinstance(type, TMaybe):
        return Maybe(None)
    if isinstance(type, TBool):
        return False
    if isinstance(type, TString):
        return ""
    if isinstance(type, TBag):
        return Bag()
    if isinstance(type, TMap):
        return Map(type, mkval(type.v))
    if isinstance(type, TEnum):
        return type.cases[0]
    if isinstance(type, TRecord):
        return FrozenDict({ f:mkval(t) for (f, t) in type.fields })
    if isinstance(type, THandle):
        return Handle(0, mkval(type.value_type))
    if isinstance(type, TTuple):
        return tuple(mkval(t) for t in type.ts)
    raise NotImplementedError(type)

@typechecked
def construct_value(t : Type) -> Exp:
    """
    Construct an expression e such that
    eval(construct_value(t), {}) == mkval(t)
    """
    if is_numeric(t):
        e = ENum(0)
    elif t == BOOL:
        e = F
    elif t == STRING:
        e = EStr("")
    elif isinstance(t, TBag):
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
    else:
        raise NotImplementedError(pprint(t))
    e = e.with_type(t)
    assert eval(e, {}) == mkval(t)
    return e
