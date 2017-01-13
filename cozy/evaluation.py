from collections import defaultdict
from functools import total_ordering

from cozy.target_syntax import *
from cozy.common import Visitor, FrozenDict, all_distinct

class HoleException(Exception):
    def __init__(self, hole, env):
        self.hole = hole
        self.env = env

@total_ordering
class hashable_defaultdict(defaultdict):
    def __hash__(self):
        return hash(tuple(sorted(self.items())))
    def __repr__(self):
        return repr(dict(self))
    def __str__(self):
        return repr(self)
    def __lt__(self, other):
        return tuple(sorted(self.items())) < tuple(sorted(other.items()))

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

class Evaluator(Visitor):
    def visit_EVar(self, v, env):
        return env[v.id]
    def visit_EHole(self, e, env):
        raise HoleException(e, dict(env))
    def visit_ENum(self, n, env):
        return n.val
    def visit_EBool(self, b, env):
        return b.val
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
    def visit_ECond(self, e, env):
        if self.visit(e.cond, env):
            return self.visit(e.then_branch, env)
        else:
            return self.visit(e.else_branch, env)
    def visit_EEnumEntry(self, val, env):
        # return val.type.cases.index(val.name)
        return val.name
    def visit_EGetField(self, e, env):
        lhs = self.visit(e.e, env)
        if isinstance(e.e.type, THandle):
            assert e.f == "val"
            return lhs[1]
        return lhs[e.f]
    def visit_EUnaryOp(self, e, env):
        if e.op == "not":
            return not self.visit(e.e, env)
        elif e.op == "sum":
            return sum(self.visit(e.e, env))
        elif e.op == "unique":
            return all_distinct(self.visit(e.e, env))
        elif e.op == "the":
            bag = self.visit(e.e, env)
            if bag:
                return Maybe(bag[0])
            else:
                return self.visit(ENull().with_type(e.type), env)
        else:
            raise NotImplementedError(e.op)
    def visit_EBinOp(self, e, env):
        if e.op == "and":
            return self.visit(e.e1, env) and self.visit(e.e2, env)
        elif e.op == "or":
            return self.visit(e.e1, env) or self.visit(e.e2, env)
        elif e.op == "==":
            return self.visit(e.e1, env) == self.visit(e.e2, env)
        elif e.op == "+":
            return self.visit(e.e1, env) + self.visit(e.e2, env)
        elif e.op == "-":
            return self.visit(e.e1, env) - self.visit(e.e2, env)
        elif e.op == "<":
            return self.visit(e.e1, env) < self.visit(e.e2, env)
        elif e.op == ">":
            return self.visit(e.e1, env) > self.visit(e.e2, env)
        elif e.op == "<=":
            return self.visit(e.e1, env) <= self.visit(e.e2, env)
        elif e.op == ">=":
            return self.visit(e.e1, env) >= self.visit(e.e2, env)
        elif e.op == "in":
            return self.visit(e.e1, env) in self.visit(e.e2, env)
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
        env2 = dict(env)
        env2[lam.arg.id] = arg
        return self.visit(lam.body, env2)
    def visit_EAlterMaybe(self, e, env):
        x = self.visit(e.e, env)
        if x.obj is not None:
            x = Maybe(self.eval_lambda(e.f, x.obj, env))
        return x
    def visit_EMakeMap(self, e, env):
        im = defaultdict(Bag)
        for x in self.visit(e.e, env):
            im[self.eval_lambda(e.key, x, env)] += Bag((x,))
        res = hashable_defaultdict(lambda: self.eval_lambda(e.value, Bag(), env))
        for (k, es) in im.items():
            res[k] = self.eval_lambda(e.value, es, env)
        return res
    def visit_EMapGet(self, e, env):
        return self.visit(e.map, env)[self.visit(e.key, env)]
    def visit_EMap(self, e, env):
        return Bag(self.eval_lambda(e.f, x, env) for x in self.visit(e.e, env))
    def visit_EFilter(self, e, env):
        return Bag(x for x in self.visit(e.e, env) if self.eval_lambda(e.p, x, env))
    def visit_EFlatten(self, e, env):
        res = self.visit(e.e, env)
        return Bag(elem for bag in res for elem in bag)
    def visit_EFlatMap(self, e, env):
        return self.visit(EFlatten(EMap(e.e, e.f)), env)
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
    def visit_Exp(self, e, env):
        raise NotImplementedError("eval({})".format(e))
    def visit_object(self, o, *args):
        raise Exception("cannot eval {}".format(repr(o)))
    def visit(self, o, *args):
        try:
            return super().visit(o, *args)
        except:
            print("evaluation of {} failed".format(repr(o)))
            raise

def eval(e, env):
    return Evaluator().visit(e, env)

def mkval(type):
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
        return hashable_defaultdict(int)
    if isinstance(type, TEnum):
        return type.cases[0]
    if isinstance(type, TRecord):
        return FrozenDict({ f:mkval(t) for (f, t) in type.fields })
    if isinstance(type, THandle):
        return (0, mkval(type.value_type))
    if isinstance(type, TTuple):
        return tuple(mkval(t) for t in type.ts)
    raise NotImplementedError(type)

class EnvCollector(Evaluator):
    def __init__(self, hole_name):
        self.hole_name = hole_name
        self.envs = []
    def visit_EHole(self, e, env):
        if e.name == self.hole_name:
            self.envs.append(dict(env))
        return mkval(e.type)

def all_envs_for_hole(e, env, hole_name):
    x = EnvCollector(hole_name)
    x.visit(e, env)
    return x.envs
