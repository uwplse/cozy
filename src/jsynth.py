from collections import namedtuple, deque, defaultdict
import datetime
import sys

from syntax import *
from syntax_tools import subst, pprint, free_vars
from common import Visitor, fresh_name, declare_case, typechecked

VALID = object()
NEW = object()
OLD = object()

class Builder(object):
    def build(self, cache, size):
        raise NotImplementedError()

class Counterexample(Exception):
    def __init__(self, value):
        self.value = value

class HoleException(Exception):
    def __init__(self, hole, env):
        self.hole = hole
        self.env = env

def find_subgoals(e):
    class V(Visitor):
        def visit_EVar(self, e):
            return ()
        def visit_ENum(self, e):
            return ()
        def visit_EUnaryOp(self, e):
            return self.visit(e.e)
        def visit_EBinOp(self, e):
            yield from self.visit(e.e1)
            yield from self.visit(e.e2)
        def visit_EHole(self, e):
            yield (e.name, e.type, e.builder)
        def visit_EListComprehension(self, e):
            yield from self.visit(e.e)
            for clause in e.clauses:
                yield from self.visit(clause)
        def visit_CPull(self, e):
            return self.visit(e.e)
        def visit_CCond(self, e):
            return self.visit(e.e)
        def visit_EGetField(self, e):
            return self.visit(e.e)
        def visit_EMap(self, e):
            yield from self.visit(e.e)
            yield from self.visit(e.f)
        def visit_EApp(self, e):
            yield from self.visit(e.f)
            yield from self.visit(e.arg)
        def visit_EMakeMap(self, e):
            yield from self.visit(e.e)
            yield from self.visit(e.key)
            yield from self.visit(e.value)
        def visit_EMapGet(self, e):
            yield from self.visit(e.map)
            yield from self.visit(e.key)
        def visit_ELambda(self, e):
            return self.visit(e.body)
        def visit_Exp(self, e):
            raise NotImplementedError("find_subgoals({})".format(e))
        def visit_object(self, o):
            raise Exception("cannot find subgoals in {}".format(repr(o)))
    return V().visit(e)

def contains_holes(e):
    for g in find_subgoals(e):
        return True
    return False

class hashable_defaultdict(defaultdict):
    def __init__(self, k):
        super().__init__(k)
    def __hash__(self):
        return hash(tuple(sorted(self.items())))
    def __repr__(self):
        return repr(dict(self))
    def __str__(self):
        return repr(self)

class Evaluator(Visitor):
    def visit_EVar(self, v, env):
        return env[v.id]
    def visit_EHole(self, e, env):
        raise HoleException(e, dict(env))
    def visit_ENum(self, n, env):
        return n.val
    def visit_EGetField(self, e, env):
        return self.visit(e.e, env)[e.f]
    def visit_EUnaryOp(self, e, env):
        if e.op == "not":
            return not self.visit(e.e, env)
        elif e.op == "sum":
            return sum(self.visit(e.e, env))
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
        else:
            raise NotImplementedError(e.op)
    def visit_EApp(self, e, env):
        return self.eval_lambda(e.f, self.visit(e.arg, env), env)
    def visit_EListComprehension(self, e, env):
        return tuple(self.visit_clauses(e.clauses, e.e, env))
    def eval_lambda(self, lam, arg, env):
        env2 = dict(env)
        env2[lam.arg.id] = arg
        return self.visit(lam.body, env2)
    def visit_EMakeMap(self, e, env):
        im = defaultdict(tuple)
        for x in self.visit(e.e, env):
            im[self.eval_lambda(e.key, x, env)] += (x,)
        res = hashable_defaultdict(lambda: self.eval_lambda(e.value, (), env))
        for (k, es) in im.items():
            res[k] = self.eval_lambda(e.value, es, env)
        return res
    def visit_EMapGet(self, e, env):
        return self.visit(e.map, env)[self.visit(e.key, env)]
    def visit_EMap(self, e, env):
        return tuple(self.eval_lambda(e.f, x, env) for x in self.visit(e.e, env))
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
def eval(e, env):
    return Evaluator().visit(e, env)

def mkval(type):
    if isinstance(type, TInt) or isinstance(type, TLong):
        return 0
    if isinstance(type, TBool):
        return False
    if isinstance(type, TBag):
        return ()
    if isinstance(type, TMap):
        return hashable_defaultdict(int)
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

TBitVec = declare_case(Type, "TBitVec", ["width"])

def satisfy(e):
    print("sat? {}".format(pprint(e)))
    # print(repr(e))

    import z3
    ctx = z3.Context()
    solver = z3.Solver(ctx=ctx)

    DEPTH = 2
    def mkvar(type):
        if type == TInt() or type == TLong():
            return z3.Int(fresh_name(), ctx=ctx)
        if type == TBool():
            return z3.Bool(fresh_name(), ctx=ctx)
        if isinstance(type, TBitVec):
            return z3.BitVec(fresh_name(), type.width, ctx=ctx)
        elif isinstance(type, TBag):
            mask = [mkvar(TBool()) for i in range(DEPTH)]
            elems = [mkvar(type.t) for i in range(DEPTH)]
            # symmetry breaking
            for i in range(len(mask) - 1):
                solver.add(z3.Implies(mask[i], mask[i+1], ctx))
            return (mask, elems)
        elif isinstance(type, TRecord):
            return { field : mkvar(t) for (field, t) in type.fields }
        else:
            raise NotImplementedError(type)

    def reconstruct(model, value, type):
        if type == TInt() or type == TLong():
            return model.eval(value, model_completion=True).as_long()
        if type == TBool():
            return bool(model.eval(value, model_completion=True))
        if isinstance(type, TBitVec):
            return model.eval(value, model_completion=True)
        elif isinstance(type, TBag):
            mask, elems = value
            real_val = ()
            for i in range(len(elems)):
                if reconstruct(model, mask[i], TBool()):
                    real_val += (reconstruct(model, elems[i], type.t),)
            return real_val
        elif isinstance(type, TRecord):
            res = hashable_defaultdict(lambda: None)
            for (field, t) in type.fields:
                res[field] = reconstruct(model, value[field], t)
            return res
        else:
            raise NotImplementedError(type)

    _env = { }
    fvs = free_vars(e)
    for v in fvs:
        # print("{} : {}".format(pprint(v), pprint(v.type)))
        _env[v.id] = mkvar(v.type)
    # print(_env)

    class V(Visitor):
        def visit_EVar(self, v, env):
            return env[v.id]
        def visit_ENum(self, n, env):
            return n.val
        def visit_EUnaryOp(self, e, env):
            if e.op == "not":
                return z3.Not(self.visit(e.e, env), ctx=ctx)
            elif e.op == "sum":
                bag_mask, bag_elems = self.visit(e.e, env)
                sum = 0
                for i in range(len(bag_elems)):
                    sum = z3.If(bag_mask[i], bag_elems[i], 0, ctx=ctx) + sum
                return sum
            else:
                raise NotImplementedError(e.op)
        def visit_EGetField(self, e, env):
            r = self.visit(e.e, env)
            return r[e.f]
        def visit_EBinOp(self, e, env):
            if e.op == "and":
                return z3.And(self.visit(e.e1, env), self.visit(e.e2, env), ctx=ctx)
            elif e.op == "or":
                return z3.Or(self.visit(e.e1, env), self.visit(e.e2, env), ctx=ctx)
            elif e.op == "==":
                return self.visit(e.e1, env) == self.visit(e.e2, env)
            elif e.op == "+":
                return self.visit(e.e1, env) + self.visit(e.e2, env)
            else:
                raise NotImplementedError(e.op)
        def visit_EListComprehension(self, e, env):
            x = self.visit_clauses(e.clauses, e.e, env)
            # print("{} ==> {}".format(pprint(e), x))
            return self.visit_clauses(e.clauses, e.e, env)
        def visit_EMap(self, e, env):
            bag_mask, bag_elems = self.visit(e.e, env)
            res_elems = []
            for x in bag_elems:
                res_elems.append(self.apply(e.f, x, env))
            return bag_mask, res_elems
        def visit_EMakeMap(self, e, env):
            bag_mask, bag_elems = self.visit(e.e, env)
            ks = [ self.apply(e.key, x, env) for x in bag_elems ]
            x = EVar(fresh_name()).with_type(e.e.type.t)
            m = {"mapping": [(k, self.apply(
                e.value,
                self.visit(
                    EListComprehension(x,
                        (CPull(x.id, bag),
                         CCond(EBinOp(e.key.apply_to(x), "==", k)))),
                    env),
                env)) for k in ks],
                "default": e.value}
            return m
        def visit_EMapGet(self, e, env):
            map = self.visit(e.map, env)
            key = self.visit(e.key, env)
            res = self.apply(map["default"], ((), ()), env)
            for (k, v) in map["mapping"]:
                res = z3.If(k == key, v, res)
            return res
        def visit_EApp(self, e, env):
            return self.apply(e.f, self.visit(e.arg, env), env)
        def apply(self, lam, arg, env):
            env2 = dict(env)
            env2[lam.arg.id] = arg
            return self.visit(lam.body, env2)
        def visit_clauses(self, clauses, e, env):
            if not clauses:
                return [True], [self.visit(e, env)]
            c = clauses[0]
            if isinstance(c, CCond):
                bag_mask, bag_elems = self.visit_clauses(clauses[1:], e, env)
                res_mask = []
                for i in range(len(bag_elems)):
                    incl_this = z3.And(bag_mask[i], self.visit(c.e, env), ctx)
                    res_mask += [incl_this]
                return res_mask, bag_elems
            elif isinstance(c, CPull):
                bag_mask, bag_elems = self.visit(c.e, env)
                res_mask, res_elems = [], []
                for i in range(len(bag_elems)):
                    incl_this = bag_mask[i]
                    env2 = dict(env)
                    env2[c.id] = bag_elems[i]
                    bag2_mask, bag2_elems = self.visit_clauses(clauses[1:], e, env2)
                    res_mask += [z3.And(incl_this, bit, ctx) for bit in bag2_mask]
                    res_elems += bag2_elems
                return res_mask, res_elems
        def visit_Exp(self, e, *args):
            raise NotImplementedError("toZ3({})".format(e))
        def visit_AstRef(self, e, env):
            """AstRef is the Z3 AST node type"""
            return e

    solver.add(V().visit(e, _env))
    # print(solver.assertions())
    res = solver.check()
    if res == z3.unsat:
        return None
    elif res == z3.unknown:
        raise Exception("z3 reported unknown")
    else:
        model = solver.model()
        # print(model)
        res = { }
        for v in fvs:
            res[v.id] = reconstruct(model, _env[v.id], v.type)
        # print(res)
        return res

def pick_to_sum(n, total_size):
    if n == 0:
        assert total_size == 0, "total size is {}".format(total_size)
        yield ()
        return
    if n == 1:
        yield (total_size,)
        return
    for size in range(1, total_size - n + 2):
        for rest in pick_to_sum(n - 1, total_size - size):
            yield (size,) + rest

def pick(caches, types, sizes):
    if len(caches) == 0:
        yield ()
    else:
        for e in caches[0].find(type=types[0], size=sizes[0]):
            for es in pick(caches[1:], types[1:], sizes[1:]):
                yield (e,) + es

def nested_dict(n, t):
    if n <= 0:
        return t()
    return defaultdict(lambda: nested_dict(n-1, t))

class Cache(object):
    def __init__(self):
        self.data = nested_dict(3, list) # data[type_tag][type][size] is list of exprs
        self.seen = set()
    def tag(self, t):
        return type(t)
    def is_tag(self, t):
        return isinstance(t, type)
    def add(self, e, size):
        self.data[self.tag(e.type)][e.type][size].append(e)
    def find(self, type=None, size=None):
        type_tag = None
        if self.is_tag(type):
            type_tag = type
            type = None
        res = []
        for x in (self.data.values() if type_tag is None else [self.data.get(type_tag, {})]):
            for y in (x.values() if type is None else [x.get(type, {})]):
                for z in (y.values() if size is None else [y.get(size, [])]):
                    res += z
        return res

Solution = namedtuple("Solution", ["exps"])
PartialSolution = namedtuple("PartialSolution", ["examples", "spec", "k"])
EHole = declare_case(Exp, "EHole", ["name", "type", "builder"])
EMakeMap = declare_case(Exp, "EMakeMap", ["e", "key", "value"])
EMapGet = declare_case(Exp, "EMapGet", ["map", "key"])
EMap = declare_case(Exp, "EMap", ["e", "f"])
EApp = declare_case(Exp, "EApp", ["f", "arg"])

# @typechecked
# def joint_synthesize(
#         spec      : Exp,
#         examples  = None,
#         timeout   = None,
#         k         = lambda exps: exps):

#     goals = list(find_subgoals(spec))
#     start = None

#     def resume():
#         nonlocal start
#         print("working on: {}".format(pprint(spec)))
#         start = datetime.datetime.now()

#     def timedout():
#         if timeout is None:
#             return False
#         return datetime.datetime.now() > (start + timeout)

#     resume()

#     examples = examples or []
#     while True:
#         # print("#examples={}".format(len(examples)))

#         # init caches
#         caches = [Cache() for _ in goals]

#         try:

#             size = 1
#             while True:
#                 print("  size={}".format(size))

#                 # build new expressions
#                 for i in range(len(goals)):
#                     name, _, builder = goals[i]
#                     cache = caches[i]
#                     for candidate in builder.build(cache, size):
#                         if timedout():
#                             yield
#                         cache.add(candidate, size=size)

#                 # search for a solution set
#                 for split in pick_to_sum(len(caches), size):
#                     for exps in pick(caches, [type for (_, type, _) in goals], split):
#                         if timedout():
#                             yield
#                         # print(exps, [type for (_, type, _) in goals])
#                         new_spec = subst(spec, { name : e for ((name, _, _), e) in zip(goals, exps) })
#                         subgoals = list(find_subgoals(new_spec))

#                         # this candidate might be a complete solution
#                         if not subgoals:
#                             ok = all(eval(new_spec, ex) for ex in examples)
#                             if ok:
#                                 model = satisfy(EUnaryOp("not", new_spec).with_type(TBool()))
#                                 if model is not None:
#                                     print("new example: {}".format(model))
#                                     raise Counterexample(model)
#                                 else:
#                                     yield Solution(k(exps))
#                                     resume()

#                         # it is unclear whether this candidate is valid---need to solve subgoals
#                         else:
#                             es = exps
#                             sgs = subgoals
#                             def kk(sub_exps):
#                                 exps2 = k(tuple(subst(e, { name : sub_e for ((name, _, _), sub_e) in zip(sgs, sub_exps) }) for e in es))
#                                 # print("   spec {} ==> {}".format(pprint(spec), pprint(new_spec)))
#                                 print("   with {}: {} ===> {}".format(sub_exps, es, exps2))
#                                 return exps2
#                                 # return k(tuple(subst(e, { name : sub_e for ((name, _, _), sub_e) in zip(subgoals, sub_exps) }) for e in exps))
#                             yield PartialSolution(
#                                 examples=examples,
#                                 spec=new_spec,
#                                 k=kk)
#                             resume()

#                 size += 1

#         except Counterexample as cex:
#             examples.append(cex.value)

@typechecked
def enum_types(size : int):
    if size <= 0:
        return
    elif size == 1:
        yield TInt()
        yield TBool()
    else:
        for t in enum_types(size - 1):
            yield TBag(t)
        for k in enum_types(1):
            for v in enum_types(size - 2):
                yield TMap(k, v)
                # TODO: allow record types as map keys

def distinct_exps(builder, examples, size, type):
    cache = Cache()
    seen = set()
    def fingerprint(e):
        return (e.type,) + tuple(eval(e, ex) for ex in examples)
    for i in range(size + 1):
        # if not cache.find(size=i):
        for e in builder.build(cache, i):
            if contains_holes(e):
                cache.add(e, size=i)
                continue
            fp = fingerprint(e)
            # print("fp({}) = {}".format(pprint(e), fp))
            if fp not in seen:
                seen.add(fp)
                cache.add(e, size=i)
    return cache.find(type=type, size=size)

def pick_goal(spec, examples):
    assert contains_holes(spec), "no subgoals in {}".format(spec)
    scores = defaultdict(int)
    for ex in examples:
        try:
            eval(spec, ex)
        except HoleException as e:
            scores[e.hole.name] += 1
    if not scores:
        for g in find_subgoals(spec):
            return g[0]
    return max(scores.keys(), key=scores.get)

def construct_inputs(spec, goal_name, examples):
    # TODO: this doesn't handle the case where the hole is eval'd multiple times!
    for ex in examples:
        yield from all_envs_for_hole(spec, ex, goal_name)

def diagonalize(iterables):
    """
    Given a (potentially infinite) set of iterables, this function
    yields elements from all iterables in a "fair" manner, such that
    even if one of the iterables yields an infinite number of elements,
    every element from every iterable is guaranteed to be reached
    in a finite number of steps.
    """
    wq = deque()
    wq.append(iterables)
    while wq:
        it = wq.pop()
        try:
            if it is iterables:
                x = next(it)
                wq.appendleft(x)
                wq.appendleft(it)
            else:
                x = next(it)
                yield x
                wq.appendleft(it)
        except StopIteration:
            pass

def nats(prefix=None):
    i = 0
    while True:
        yield "{}_{}".format(prefix, i) if prefix is not None else str(i)
        i += 1

indent = ""

def find_consistent_exps(
        spec     : Exp,
        examples : [Exp],
        size     : int = None,
        cache    : Cache = None,
        seen     : set = None):

    if cache is None:
        cache = Cache()
    if seen is None:
        seen = set()

    global indent
    old_indent = indent
    indent = indent + "  "

    try:
        # print("{}find({}, {})".format(indent, pprint(spec), size))

        goals = list(find_subgoals(spec))

        if not goals:
            if size == 0 and all(eval(spec, ex) for ex in examples):
                print("final: {}".format(pprint(spec)))
                yield { }
            else:
                # if size != 0:
                #     # print("REJECTED (wrong size): {}".format(pprint(spec)))
                #     pass
                # else:
                #     print("  REJECTED: {} [examples={}]".format(pprint(spec), examples))
                pass
            return

        if size is None:
            size = 1
            while True:
                # print("size={}".format(size))
                yield from find_consistent_exps(spec, examples, size, cache=cache, seen=seen)
                size += 1
            return

        # not strictly necessary, but this helps
        if len(goals) > size:
            return

        name = pick_goal(spec, examples)
        _, type, builder = [goal for goal in goals if goal[0] == name][0]
        goals = [goal for goal in goals if goal[0] != name]
        g_examples = list(construct_inputs(spec, name, examples))

        # print("{}#####".format(indent))
        for (sz1, sz2) in pick_to_sum(2, size + 1):
            yield
            sz2 -= 1
            # print("{}({},{})".format(indent, sz1, sz2))
            for e in distinct_exps(builder, g_examples, size=sz1, type=type):
                # print("{}| considering {} for {} [examples={}]".format(indent, pprint(e), name, g_examples))
                for d in find_consistent_exps(subst(spec, { name : e }), examples, sz2, cache=cache, seen=seen):
                    # TODO: double-check consistency
                    if d is not None:
                        d[name] = e
                    yield d
    finally:
        indent = old_indent

def synth(spec):
    examples = []
    while True:
        for mapping in find_consistent_exps(spec, examples):
            if mapping is None:
                yield
                continue

            new_spec = spec
            while contains_holes(new_spec):
                prev_spec = new_spec
                new_spec = subst(new_spec, mapping)
                assert new_spec != prev_spec, "failed to converge: {}, {}".format(new_spec, mapping)

            print("considering: {}".format(pprint(new_spec)))
            if all(eval(new_spec, ex) for ex in examples):
                model = satisfy(EUnaryOp("not", new_spec).with_type(TBool()))
                if model is not None:
                    print("new example: {}".format(model))
                    examples.append(model)
                    yield
                    break
                else:
                    yield mapping
            else:
                assert False
                print("rejected: {}".format(pprint(new_spec)))

if __name__ == "__main__":
    # Next steps:
    #   - eliminate caches in favor of pure enumeration?
    #   - find a way to bias towards the right answer

    INT = TInt()
    LONG = TLong()
    BOOL = TBool()
    REC = TRecord((("key", INT), ("value", INT)))
    bag = EVar("bag").with_type(TBag(REC))
    v = EVar("x").with_type(REC)
    arg = EVar("k").with_type(INT)
    target = EUnaryOp("sum", EListComprehension(EGetField(v, "value"), (CPull(v.id, bag), CCond(EBinOp(EGetField(v, "key"), "==", arg))))).with_type(INT)

    class B(Builder):
        def __init__(self, roots):
            self.roots = roots
        def build(self, cache, size):
            if size == 1:
                # for r in self.roots:
                #     print(" {} : {};".format(pprint(r), pprint(r.type)), end="")
                # print()
                yield from self.roots
                return
            for e in cache.find(type=TRecord, size=size-1):
                for (f,t) in e.type.fields:
                    yield EGetField(e, f).with_type(t)
            for e in cache.find(type=TBag(INT), size=size-1):
                yield EUnaryOp("sum", e).with_type(INT)
            for (sz1, sz2) in pick_to_sum(2, size - 1):
                for a1 in cache.find(type=INT, size=sz1):
                    for a2 in cache.find(type=INT, size=sz2):
                        yield EBinOp(a1, "+", a2).with_type(INT)
                for m in cache.find(type=TMap, size=sz1):
                    for k in cache.find(type=m.type.k, size=sz2):
                        yield EMapGet(m, k).with_type(m.type.v)
                for t in enum_types(sz1):
                    for bag in cache.find(type=TBag, size=sz2):
                        if not isinstance(bag, EMap):
                            e = EVar(fresh_name()).with_type(bag.type.t)
                            hole = EHole(fresh_name(), t, self.with_roots([e]))
                            yield EMap(bag, ELambda(e, hole)).with_type(TBag(t))
            for (bagsize, ksize, vsize) in pick_to_sum(3, size - 1):
                for kt in enum_types(ksize):
                    for vt in enum_types(vsize):
                        for bag in cache.find(type=TBag, size=bagsize):
                            e = EVar(fresh_name()).with_type(bag.type.t)
                            es = EVar(fresh_name()).with_type(bag.type)
                            khole = EHole(fresh_name(), kt, self.with_roots([e]))
                            vhole = EHole(fresh_name(), vt, self.with_roots([es]))
                            yield EMakeMap(bag, ELambda(e, khole), ELambda(es, vhole)).with_type(TMap(kt, vt))
        def with_roots(self, new_roots):
            return B(list(new_roots) + list(self.roots))

    query_hole = EHole("query", target.type, B(free_vars(target)))
    spec = EBinOp(query_hole, "==", target)

    for mapping in synth(spec):
        if mapping is not None:

            result = query_hole
            while contains_holes(result):
                prev_result = result
                result = subst(result, mapping)
                assert result != prev_result, "failed to converge: {}, {}".format(result, mapping)

            print(pprint(result))
            break

    # timeout = datetime.timedelta(seconds=3)
    # wq = deque()
    # wq.append(joint_synthesize(spec, timeout=timeout))
    # while wq:
    #     problem = wq.pop()
    #     x = next(problem)
    #     if x is None:
    #         wq.appendleft(problem)
    #     elif isinstance(x, Solution):
    #         print("Solution:")
    #         for e in x.exps:
    #             print(" - {}".format(pprint(e)))
    #         break
    #     elif isinstance(x, PartialSolution):
    #         print("Partial: {}".format(pprint(x.spec)))
    #         wq.appendleft(joint_synthesize(x.spec, x.examples, timeout=timeout, k=x.k))
    #         wq.append(problem)
    #     else:
    #         raise NotImplementedError(x)

    # sys.exit(0)

    # def specs():
    #     state_name = fresh_name()
    #     state_builder = B(free_vars(target))
    #     state_type_complexity = 1
    #     while True:
    #         for state_type in enum_types(size=state_type_complexity):
    #             state = EVar(state_name).with_type(state_type)
    #             query_builder = state_builder.with_roots([state])
    #             yield EBinOp(EApp(
    #                 ELambda(state, EHole("query", target.type, query_builder)),
    #                 EHole("state", state_type, state_builder)), "==", target)
    #         state_type_complexity += 1

    # for step in diagonalize(synth(spec) for spec in specs()):
    #     if isinstance(step, Solution):
    #         print(step)
    #         break
