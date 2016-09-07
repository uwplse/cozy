import collections
import pickle
import re
import sys

from z3 import Context, SolverFor

from common import Visitor, fresh_name, split, declare_case, typechecked
import predicates
import plans
import syntax
from syntax_tools import free_vars, pprint, subst, alpha_equivalent
import synthesis
import cost_model
import stats
from typecheck import typecheck
import incrementalization as inc
# import aggregations
import structures

Context = collections.namedtuple("Context", ["state", "deltas"])
Goal = collections.namedtuple("Goal", ["name", "args", "e"])
Solution = collections.namedtuple("Solution", ["goal", "state", "exp", "ops"])
PartialSolution = collections.namedtuple("PartialSolution", ["solution", "subgoals"])

def abstractify(input, var, predicate):

    mapping = {}

    class V(Visitor):
        def __init__(self):
            self.pseudofields = []
            self.pseudovars = []
            self.subops = []

        def visit_EBool(self, e, as_bool=True):
            if not as_bool:
                return self.splitoff(e)
            return predicates.Bool(e.val)

        def visit_EBinOp(self, e, as_bool=True):
            if not as_bool:
                return self.splitoff(e)
            if e.op == "and":
                lhs = self.visit(e.e1)
                rhs = self.visit(e.e2)
                return predicates.And(lhs, rhs)
            if e.op == "or":
                lhs = self.visit(e.e1)
                rhs = self.visit(e.e2)
                return predicates.Or(lhs, rhs)
            if e.op in [">", ">=", "<", "<=", "==", "!="]:
                lhs = self.visit(e.e1, as_bool=False)
                rhs = self.visit(e.e2, as_bool=False)
                if e.op == ">":  op = predicates.Gt
                if e.op == ">=": op = predicates.Ge
                if e.op == "<":  op = predicates.Lt
                if e.op == "<=": op = predicates.Le
                if e.op == "==": op = predicates.Eq
                if e.op == "!=": op = predicates.Ne
                return predicates.Compare(lhs, op, rhs)
            return self.splitoff(e)

        def visit_EUnaryOp(self, e, as_bool=True):
            if not as_bool:
                return self.splitoff(e)
            if e.op == "not":
                return predicates.Not(self.visit(e.e))
            return self.splitoff(e)

        def splitoff(self, e):
            v = mapping.get(e)
            if v is None:
                args = [v for v in free_vars(e) if v.id == var or v.id in [i[0] for i in input]]
                fvs = {v.id for v in args}
                argtypes = [(arg.id, arg.type) for arg in args]
                n = fresh_name()
                v = predicates.Var(n)
                mapping[e] = v
                if fvs == {var} or not fvs:
                    self.pseudofields.append((n, argtypes, e))
                elif var not in fvs:
                    self.pseudovars.append((n, argtypes, e))
                else:
                    self.subops.append((n, argtypes, e))
            return v

        def visit_Exp(self, e, as_bool=True):
            return self.splitoff(e)

    v = V()
    p = v.visit(predicate)
    return (v.pseudofields, v.pseudovars, v.subops, p)

@typechecked
def predicate_to_exp(p : predicates.Predicate, pseudo=()) -> syntax.Exp:
    pseudo = { name : syntax.ECall(name, [syntax.EVar(argname).with_type(t) for argname,t in args]).with_type(e.type) for (name, args, e) in pseudo }
    class V(Visitor):
        def visit_Bool(self, b):
            return syntax.EBool(b.val).with_type(syntax.TBool())
        def visit_Or(self, o):
            return syntax.EBinOp(self.visit(o.lhs), "or", self.visit(o.rhs)).with_type(syntax.TBool())
        def visit_And(self, a):
            return syntax.EBinOp(self.visit(a.lhs), "and", self.visit(a.rhs)).with_type(syntax.TBool())
        def visit_Not(self, n):
            return syntax.EUnaryOp("not", self.visit(n.p)).with_type(syntax.TBool())
        def visit_Compare(self, cmp):
            if cmp.op == predicates.Gt: op = ">"
            if cmp.op == predicates.Ge: op = ">="
            if cmp.op == predicates.Lt: op = "<"
            if cmp.op == predicates.Le: op = "<="
            if cmp.op == predicates.Eq: op = "=="
            if cmp.op == predicates.Ne: op = "!="
            return syntax.EBinOp(self.visit(cmp.lhs), op, self.visit(cmp.rhs)).with_type(syntax.TBool())
        def visit_Var(self, v):
            return pseudo.get(v.name, syntax.EVar(v))
    v = V()
    cond = v.visit(p)
    return cond

def flatten(e, op):
    class V(Visitor):
        def visit_EBinOp(self, e):
            if e.op == op:
                yield from self.visit(e.e1)
                yield from self.visit(e.e2)
            else:
                yield e
        def visit_Exp(self, e):
            yield e
    return V().visit(e)

def simplify(e):
    class V(Visitor):
        def visit_EBool(self, b):
            return b
        def visit_ENum(self, n):
            return n
        def visit_EVar(self, v):
            return v
        def visit_EUnaryOp(self, op):
            e = self.visit(op.e)
            if op.op == "not" and isinstance(e, syntax.EBool):
                return syntax.EBool(not e.val)
            return syntax.EUnaryOp(op.op, e)
        def visit_EBinOp(self, op):
            op = syntax.EBinOp(
                self.visit(op.e1), op.op, self.visit(op.e2))
            if op.op == "and":
                # move ors to the top
                if isinstance(op.e1, syntax.EBinOp) and op.e1.op == "or":
                    op = syntax.EBinOp(op.e2, "and", op.e1)
                if isinstance(op.e2, syntax.EBinOp) and op.e2.op == "or":
                    op = syntax.EBinOp(
                        syntax.EBinOp(op.e1, "and", op.e2.e1), "or",
                        syntax.EBinOp(op.e1, "and", op.e2.e2))
                    return self.visit(op)

                parts = list(p for p in flatten(op, "and") if p != syntax.EBool(True).with_type(syntax.TBool()))
                print(parts)
                if any(p == syntax.EBool(False) for p in parts):
                    return syntax.EBool(False)
                for x in parts:
                    if any(alpha_equivalent(x, syntax.EUnaryOp("not", part)) for part in parts):
                        return syntax.EBool(False)
                if len(parts) == 0: return syntax.EBool(True).with_type(syntax.TBool())
                if len(parts) == 1: return parts[0]
                res = parts[0]
                for i in range(1, len(parts)):
                    res = syntax.EBinOp(res, "and", parts[i])
                return res
            elif op.op == "in":
                e1 = self.visit(op.e1)
                e2 = self.visit(op.e2)
                if isinstance(e2, syntax.EBinOp) and e2.op == "union":
                    lhs = syntax.EBinOp(e1, "in", e2.e1)
                    rhs = syntax.EBinOp(e1, "in", e2.e2)
                    return syntax.EBinOp(lhs, "or", rhs)
                elif isinstance(e2, syntax.EUnaryOp) and e2.op == "singleton":
                    return syntax.EBinOp(e1, "==", e2.e)
                elif isinstance(e2, syntax.EBinOp) and e2.op == "-":
                    return syntax.EBinOp(
                        syntax.EBinOp(e1, "in", e2.e1), "and",
                        syntax.EUnaryOp("not", syntax.EBinOp(e1, "in", e2.e2)))
            return op
        def visit_EListComprehension(self, lcmp):
            clauses = [self.visit(c) for c in lcmp.clauses]
            if any(c == syntax.CCond(syntax.EBool(False)) for c in clauses):
                return syntax.EEmptyList()
            return syntax.EListComprehension(
                self.visit(lcmp.e),
                clauses)
        def visit_CPull(self, pull):
            return syntax.CPull(pull.id, self.visit(pull.e))
        def visit_CCond(self, cond):
            return syntax.CCond(self.visit(cond.e))
        def visit_EGetField(self, e):
            return syntax.EGetField(self.visit(e.e), e.f).with_type(e.type)
        def visit_Exp(self, e):
            print("*** WARNING: not sure how to simplify {}".format(pprint(e)))
            return e
    return V().visit(e)

@stats.task
def synthesize(spec, timeout=None):

    # Pull the spec apart a little
    state = spec.statevars
    ops = [m for m in spec.methods if isinstance(m, syntax.Op)]
    ds = [inc.to_delta(m) for m in ops]
    context = Context(state=state, deltas=ds)
    goals = [
        Goal(name=m.name, args=m.args, e=m.ret)
        for m in spec.methods if isinstance(m, syntax.Query)]

    # Initialize work queue
    q = collections.deque()
    for g in goals:
        q.append(g)

    solutions = []
    while q:
        print("###### queue len = {}".format(len(q)))
        g = q.popleft()
        e = simplify(g.e)
        print("---> solving {}".format(g.name))

        for sln in solutions:
            if alpha_equivalent(sln.goal.e, e):
                print("####### already exists: {} as {}".format(e, sln.goal.name))
                e = None
                break

        if e is None:
            solutions.append(Solution(goal=g, state=(), exp=sln.exp, ops=[syntax.SNoOp() for d in ds]))
            continue

        errs = typecheck(e, list(g.args) + list(state))
        if errs:
            print("Internal consistency problem: there are type errors in {}".format(pprint(e)))
            for e in errs:
                print("  - {}".format(e))
            sys.exit(1)
        print("####### synthesizing: {}({}) = {} = {}".format(g.name, g.args, pprint(g.e), pprint(e)))
        g = g._replace(e=e)
        psoln = synth_simple(structures.Library(), context, g, timeout)
        print("####### got: {}".format(psoln))
        solutions.append(psoln.solution)
        for subgoal in psoln.subgoals:
            q.append(subgoal)


    for sln in solutions:
        print("{:10}: {}".format(sln.goal.name, pprint(sln.exp)))
        for name,ty in sln.state:
            print("    {} : {}".format(name, pprint(ty)))

    return syntax.Spec(
        spec.name,
        spec.types,
        [v for sln in solutions for v in sln.state],
        (),
        [syntax.Op(ops[i].name, ops[i].args, (), syntax.seq([sln.ops[i] for sln in solutions])) for i in range(len(ops))] +
        [syntax.Query(sln.goal.name, sln.goal.args, (), sln.exp) for sln in solutions])

def combined_predicate(lcmp):
    l = syntax.EBool(True).with_type(syntax.TBool())
    for c in lcmp.clauses:
        # TODO: alpha renaming
        if isinstance(c, syntax.CCond):
            l = syntax.EBinOp(l, "and", c.e)
    return l

def find_the_only_pull(lcmp):
    pull = None
    nfound = 0
    for c in lcmp.clauses:
        if isinstance(c, syntax.CPull):
            pull = c
            nfound += 1
    return pull if nfound == 1 else None

def break_and(e):
    if isinstance(e, syntax.EBinOp) and e.op == "and":
        yield from break_and(e.e1)
        yield from break_and(e.e2)
    else:
        yield e

def break_list_comprehension(lcmp):
    pulls = []
    conds = []
    for clause in lcmp.clauses:
        if isinstance(clause, syntax.CPull):
            pulls.append(clause)
        elif isinstance(clause, syntax.CCond):
            conds += list(break_and(clause.e))
    return (lcmp.e, pulls, conds)

@stats.task
@typechecked
def synth_simple(library : structures.Library, context : Context, goal : Goal, timeout=None):
    statedict = dict(context.state)
    deltas = context.deltas
    no_delta = [syntax.SNoOp() for d in deltas]
    e = goal.e
    if isinstance(e, syntax.EUnaryOp):
        if isinstance(e.e, syntax.EListComprehension):
            pull = find_the_only_pull(e.e)
            if pull:
                pred = combined_predicate(e.e)
                if pred and isinstance(pull.e, syntax.EVar) and pull.e.id in statedict:
                    coll = syntax.ECall("Mapped", [pull.e, ELambda(pull.id, e.e.e)]).with_type(syntax.TBag(e.e.e.type))
                    return synthesize_1d(library, goal, goal.args, pull.id, coll, pred, e.op, deltas)

            lcmp = e.e
            parts = break_list_comprehension(lcmp)
            print("............. ----> {}".format(parts))
            exp, pulls, conds = parts

            if len(pulls) == 0:
                return PartialSolution(
                    solution=Solution(goal, (), syntax.ECall("empty_collection", []), no_delta), # TODO: for-each loop??
                    subgoals=[])
            elif len(pulls) == 1:
                # ack, we are reduced to computing this entirely on-demand
                cond = combined_predicate(e.e)
                cond_goal = Goal(
                    name=fresh_name(),
                    args=[(v.id, v.type) for v in free_vars(cond)],
                    e=cond)
                return PartialSolution(
                    solution=Solution(goal, (), syntax.EUnaryOp(e.op, syntax.EListComprehension(e.e.e, [pulls[0], syntax.ECall(cond_goal, [syntax.EVar(id) for id,type in goal.args])])), no_delta),
                    subgoals=[cond_goal])
            else:
                bound_vars = {pull.id for pull in pulls[1:]}
                left_conds = []
                right_conds = []
                for c in conds:
                    fvs = { fv.id for fv in free_vars(c) }
                    if bound_vars & fvs:
                        right_conds.append(syntax.CCond(c))
                    else:
                        left_conds.append(syntax.CCond(c))

                g1 = Goal(
                    name=fresh_name(),
                    args=goal.args,
                    e=syntax.EListComprehension(syntax.EVar(pulls[0].id), [pulls[0]] + left_conds))

                g2 = Goal(
                    name=fresh_name(),
                    args=[(pulls[0].id, pulls[0].e.type.t)] + goal.args,
                    e=syntax.EListComprehension(exp, pulls[1:] + right_conds))

                return PartialSolution(
                    solution=Solution(goal, (), syntax.ECall("for_each", [syntax.EVar(pulls[0].id), syntax.ECall(g1.name, []), syntax.ECall(g2.name, [])]), no_delta),
                    subgoals=[g1, g2])

        elif isinstance(e.e, syntax.EVar) and e.e.id in statedict:
            n = fresh_name()
            return synth_simple(context, Goal(
                name=goal.name,
                args=goal.args,
                e=syntax.EUnaryOp(e.op, syntax.EListComprehension(syntax.EVar(n).with_type(e.e.type.t), [syntax.CPull(n, e.e)]))), timeout)
        elif isinstance(e.e, syntax.EEmptyList):
            return PartialSolution(Solution(goal, (), emptycase(agg), no_delta), ())
        else:
            raise NotImplementedError(pprint(e))
        # n = fresh_name()
        # fvs = [fv for fv in free_vars(e) if fv.id not in statedict]
        # args = [(fv.id, fv.type) for fv in fvs]
        # soln = syntax.EUnaryOp(e.op, syntax.ECall(n, [fv for fv in fvs]))
        # return PartialSolution(
        #     solution=Solution(goal, (), syntax.ECall(n, fvs), [syntax.SNoOp() for d in deltas]), # TODO
        #     subgoals=[Goal(name=n, args=args, e=e.e)])
    elif isinstance(e, syntax.EVar):
        if e.id in statedict:
            n = fresh_name()
            return synthesize_1d(library, goal, [], n, e, syntax.EBool(True).with_type(syntax.TBool()), "iterator", deltas)
        else:
            return PartialSolution(Solution(goal, (), e, no_delta), [])
    elif isinstance(e, syntax.ENum):
        return PartialSolution(Solution(goal, (), e, no_delta), []) # TODO
    elif isinstance(e, syntax.EListComprehension):
        g = Goal(
            name=fresh_name(),
            args=goal.args,
            e=syntax.EUnaryOp("iterator", goal.e))
        return PartialSolution(
            solution=Solution(goal, (), syntax.ECall(g.name, [syntax.EVar(v).with_type(t) for v,t in g.args]).with_type(syntax.TIterator(goal.e.type.t)), no_delta),
            subgoals=[g])
    elif isinstance(e, syntax.EGetField):
        g = Goal(
            name=fresh_name(),
            args=goal.args,
            e=e.e)
        return PartialSolution(
            solution=Solution(
                goal,
                (),
                syntax.EGetField(syntax.ECall(g.name, [syntax.EVar(a).with_type(t) for a,t in goal.args]).with_type(e.e.type), e.f).with_type(e.type),
                no_delta),
            subgoals=[g])

    # return PartialSolution(
    #     solution=Solution(goal, (), syntax.ECall("not_implemented", [e]), [syntax.SNoOp() for d in deltas]), # TODO: for-each loop??
    #     subgoals=[])
    # raise NotImplementedError("no idea how to synthesize {}".format(pprint(goal.e)))
    print("WARNING: no idea how to synthesize {}".format(pprint(goal.e)))
    return PartialSolution(
        solution=Solution(goal, (), goal.e, no_delta),
        subgoals=())

def old_cozy(var_names, field_names, predicate, sort_field=None, timeout=None):
    key = (tuple(sorted(var_names)), tuple(sorted(field_names)), sort_field, str(predicate))
    key = "cozy" + re.sub(r"[^\w\s]", "-", str(key))

    cache_file = "/tmp/{}.pickle".format(key)
    try:
        with open(cache_file, "rb") as f:
            plans = pickle.load(f)
        print("loaded cache file {}".format(cache_file))
        return plans
    except Exception as e:
        print("failed to load cache file {}: {}".format(cache_file, e))

    ctx = synthesis.SolverContext(
        varNames=var_names,
        fieldNames=field_names,
        cost_model=lambda plan: cost_model.cost(None, None, plan))
    plans = set(ctx.synthesizePlansByEnumeration(predicate, sort_field=sort_field, timeout=timeout))

    try:
        with open(cache_file, "wb") as f:
            pickle.dump(plans, f)
    except Exception as e:
        print("failed to save cache file {}: {}".format(cache_file, e))

    return plans

@stats.task
@typechecked
def synthesize_1d(
        library : structures.Library,
        goal : Goal,
        input : [(str, syntax.Type)],
        var : str,
        collection : syntax.Exp,
        predicate : syntax.Exp,
        agg : str,
        deltas : [(str, [(str, syntax.Type)], syntax.Exp, inc.Delta)],
        timeout=None):
    """
    Synthesize an operation over a single collection.
    ("One-dimensional" synthesis.)

    This function builds an outline of a data structure having

        abstract state L : collection
        f(i) := agg [ e | v <- L, P(v, i) ]

    where
        agg     is an aggregation (All, Sum, Min, ...)
        e       is some expression mentioning v
        P       is a predicate over elements v and input i, and P does not
                mention L. It may only mention i and v.

    The arguments to this function are:
        input       - [(id, Type)]
        agg         - an Aggregation
        var         - id of v
        collection  - (L, Type of L)
        predicate   - Exp representing P
        deltas      - list of modification ops to abstract state

    This function returns a PartialSolution for the best outline found in the
    given timeout (or for the optimal outline if timeout is None).
    """

    # print("input={}".format(input))
    # print("agg={}".format(agg))
    # print("exp={}".format(exp))
    # print("var={}".format(var))
    # print("collection={}".format(collection))
    # print("predicate={}".format(predicate))
    # print("deltas={}".format(deltas))

    # print("fvs={}".format(free_vars(predicate)))

    (pseudofields, pseudovars, subops, abstraction) = abstractify(input, var, predicate)
    uniform_subops, nonuniform_subops = split(subops, lambda s: not any(i in s[1] for i in input))
    # print("pseudofields={}".format(pseudofields))
    # print("pseudovars={}".format(pseudovars))
    # print("u_subops={}".format(uniform_subops))
    # print("n_subops={}".format(nonuniform_subops))
    # print("abstraction={}".format(abstraction))

    fnames = [f[0] for f in pseudofields] + [v[0] for v in uniform_subops]
    vnames = [v[0] for v in pseudovars]   + [v[0] for v in nonuniform_subops]
    print("Calling Cozy on {} ----> {}".format(pprint(predicate), abstraction))

    # TODO: try all?
    all_pseudo = pseudofields + pseudovars + subops
    for plan in old_cozy(vnames, fnames, abstraction, sort_field=None, timeout=None):
        subgoals = [Goal(name, args, e) for (name, args, e) in all_pseudo]

        # TODO: try all?
        sln = None
        for impl in possible_implementations(library, plan, collection, pseudofields + uniform_subops, pseudovars + nonuniform_subops, agg):

            # return PartialSolution(Solution(goal, impl.state(), impl.query(), op_impls), subgoals)
            print("{} =====>".format(plan))
            for (sn, se) in impl[0]:
                print("    {} = {}".format(sn, pprint(se)))
            print("    return {}".format(pprint(impl[1])))
            if sln is None:
                sln = impl

        if sln is not None:
            state, e = sln
            op_impls = [syntax.SNoOp()] * len(deltas)
            for i in range(len(deltas)):
                (name, args, member, d) = deltas[i]
                for (sn, se) in state:
                    (change, new_subgoals) = derivative(se, member, d)
                    op_impl = apply_change(syntax.EVar(sn).with_type(se.type), change)
                    op_impls[i] = syntax.seq([op_impls[i], op_impl])
                    subgoals += list(new_subgoals)
            return PartialSolution(Solution(goal, [(sn, se.type) for (sn, se) in state], e, op_impls), subgoals)

        raise Exception("no implementations available for {}".format(plan))
    raise Exception("no plan for {}".format(abstraction))

class LLInsertAtFront(inc.SetAdd): pass
class LLRemove(inc.SetRemove): pass
HMUpdate = declare_case(inc.Delta, "HMUpdate", ["key", "delta"])
RecordFieldUpdate = declare_case(inc.Delta, "RecordFieldUpdate", ["f", "delta"])

class AddNum(inc.Delta):
    def __init__(self, e):
        self.e = e

@typechecked
def derivative(
        e     : syntax.Exp,
        var   : syntax.EVar,
        delta : inc.Delta) -> (inc.Delta, [Goal]):
    """
    How does `e` change when `var` changes by `delta`?
    The answer may require computing some subgoals.
    """

    subgoals = []

    def derivative_ll(d):
        if isinstance(d, inc.NoDelta):
            return d
        elif isinstance(d, inc.SetAdd):
            return LLInsertAtFront(d.e)
        elif isinstance(d, inc.SetRemove):
            return LLRemove(d.e)
        elif isinstance(d, inc.Conditional):
            return inc.Conditional(
                d.cond,
                derivative_ll(d.delta))
        else:
            raise NotImplementedError(d)

    def derivative_hm(d, key_func, value_func):
        if isinstance(d, inc.NoDelta):
            return d
        elif isinstance(d, inc.SetAdd) or isinstance(d, inc.SetRemove):
            affected_key = key_func.apply_to(d.e)
            (subdelta, sgs) = derivative(value_func.body, syntax.EVar(value_func.argname), d)
            for sg in sgs:
                subgoals.append(sg)
            return HMUpdate(affected_key, subdelta)
        elif isinstance(d, inc.Conditional):
            return inc.Conditional(
                d.cond,
                derivative_hm(d.delta))
        else:
            raise NotImplementedError(d)

    def derivative_sum(d):
        if isinstance(d, inc.NoDelta):
            return d
        elif isinstance(d, inc.SetAdd):
            return AddNum(d.e)
        elif isinstance(d, inc.SetRemove):
            return AddNum(syntax.EUnaryOp("-", d.e).with_type(e.type))
        elif isinstance(d, inc.Conditional):
            return inc.Conditional(
                d.cond,
                derivative_sum(d.delta))
        else:
            raise NotImplementedError(d)

    class V(Visitor):

        def visit_EVar(self, v):
            if v == var:
                return delta
            return inc.NoDelta()

        def visit_ECall(self, call):
            func = call.func
            if func == "MakeLinkedList":
                return derivative_ll(self.visit(call.args[0]))
            if func == "MakeHashMap":
                return derivative_hm(self.visit(call.args[0]), call.args[1], call.args[2])
            elif func == "Sum":
                return derivative_sum(self.visit(call.args[0]))
            elif func == "Mapped":
                d = self.visit(call.args[0])
                if isinstance(d, inc.NoDelta):
                    return d
                elif isinstance(d, inc.SetAdd):
                    return inc.SetAdd(call.args[1].apply_to(d.e))
                elif isinstance(d, inc.SetRemove):
                    return inc.SetRemove(call.args[1].apply_to(d.e))
                else:
                    raise NotImplementedError(d)
            elif func == "Filter":
                d = self.visit(call.args[0])
                if isinstance(d, inc.NoDelta):
                    return d
                elif isinstance(d, inc.SetAdd):
                    return inc.Conditional(
                        call.args[1].apply_to(d.e),
                        inc.SetAdd(d.e))
                elif isinstance(d, inc.SetRemove):
                    return inc.Conditional(
                        call.args[1].apply_to(d.e),
                        inc.SetRemove(d.e))
                else:
                    raise NotImplementedError(d)
            else:
                raise NotImplementedError(func)

        def visit_EMakeRecord(self, e):
            return inc.multi_delta([RecordFieldUpdate(f, self.visit(ee)) for (f, ee) in e.fields])

        def visit_Exp(self, e):
            raise NotImplementedError(str(e))

    change = V().visit(e)
    return (change, subgoals)

@typechecked
def apply_change(
        x      : syntax.Exp,
        delta  : inc.Delta) -> syntax.Stm:

    class V(Visitor):
        def visit_LLInsertAtFront(self, delta):
            return syntax.SCall(x, "LLInsertAtFront", [delta.e])
        def visit_LLRemove(self, delta):
            return syntax.SCall(x, "LLRemove", [delta.e])
        def visit_HMUpdate(self, delta):
            v = syntax.EVar(fresh_name()).with_type(x.type.v)
            return syntax.seq([
                syntax.SDecl(v.id, syntax.ECall("HashMapLookup", [x, delta.key]).with_type(v.type)),
                apply_change(v, delta.delta)])
        def visit_AddNum(self, delta):
            return syntax.SAssign(x, syntax.EBinOp(x, "+", delta.e))
        def visit_Conditional(self, delta):
            substm = self.visit(delta.delta)
            return syntax.SIf(delta.cond, substm, syntax.SNoOp())
        def visit_RecordFieldUpdate(self, delta):
            return apply_change(syntax.EGetField(x, delta.f).with_type(dict(x.type.fields)[delta.f]), delta.delta)
        def visit_MultiDelta(self, delta):
            return syntax.SSeq(
                self.visit(delta.delta1),
                self.visit(delta.delta2))
        def visit_Delta(self, d):
            raise NotImplementedError(str(d))

    return V().visit(delta)

TArrayList  = declare_case(syntax.Type, "TArrayList",   ["t"])
TLinkedList = declare_case(syntax.Type, "TLinkedList",  ["t"])
THashMap    = declare_case(syntax.Type, "THashMap",     ["k", "v"])

@typechecked
def possible_implementations(
        library    : structures.Library,
        plan       : plans.Plan,
        collection : syntax.Exp,
        pseudofields,
        pseudovars,
        agg        : str = "iterator"):
    """
    yields tuples (s, e) where
        s -- list of state tuples (v : str, expr : Exp)
        e -- expression : Exp
    """
    if isinstance(plan, plans.AllWhere):
        guard = predicate_to_exp(plan.toPredicate(), pseudofields + pseudovars)
        if guard != syntax.EBool(True).with_type(syntax.TBool()):
            n = fresh_name()
            collection = syntax.ECall("Filter", [collection, ELambda(n, guard)]).with_type(collection.type) # TODO
        if agg == "iterator":
            for (f, t) in [("MakeLinkedList", TLinkedList), ("MakeArrayList", TArrayList)]:
                n = fresh_name()
                list_type = t(collection.type.t)
                s = (n, syntax.ECall(f, [collection]).with_type(list_type))
                e = syntax.ECall("Iterator", [syntax.EVar(n).with_type(list_type)]).with_type(syntax.TIterator(collection.type.t))
                yield ([s], e)
        elif agg == "sum":
            n = fresh_name()
            t = collection.type.t
            s = (n, syntax.ECall("Sum", [collection]).with_type(t))
            yield ([s], syntax.EVar(n).with_type(t))
        # elif agg == "min":
        #     yield syntax.ECall("Stored", [syntax.ECall("Min", [collection])])
        #     yield syntax.ECall("MinHeapPeek", [syntax.ECall("Stored", [syntax.ECall("MakeMinHeap", [collection])])])
        else:
            raise NotImplementedError(agg)
    elif isinstance(plan, plans.HashLookup):
        subcollection_name = fresh_name()
        subcollection = syntax.EVar(subcollection_name).with_type(collection.type)
        for (s, e) in possible_implementations(library, plan.plan, subcollection, pseudofields, pseudovars, agg):
            value_type = syntax.TRecord([(f, e.type) for (f, e) in s])
            key_type = syntax.TInt() # TODO
            x = fresh_name("x")
            key_func = ELambda(x, syntax.ENum(32).with_type(syntax.TInt())) # TODO
            lookup_key = syntax.ENum(33).with_type(syntax.TInt())          # TODO
            value_func = ELambda(subcollection_name, syntax.EMakeRecord(s))
            map_type = THashMap(key_type, value_type)
            n = fresh_name()
            new_state = (n, syntax.ECall("MakeHashMap", [collection, key_func, value_func]).with_type(map_type))
            v = fresh_name()
            let_body = subst(e, { f : syntax.EGetField(syntax.EVar(v).with_type(value_type), f) for (f, _) in s })
            new_e = syntax.ELet(v,
                syntax.ECall("HashMapLookup", [syntax.EVar(n).with_type(map_type), lookup_key]).with_type(value_type),
                let_body).with_type(let_body.type)
            yield ([new_state], new_e)
        # assert isinstance(plan.plan, plans.AllWhere)
        # for impl in possible_implementations(library, plan.plan, k, collection, pseudofields, pseudovars):
        #     key_type = syntax.TInt() # TODO
        #     key_func = lambda x: syntax.ENum(0) # TODO
        #     query_key_func = lambda args: syntax.ENum(1) # TODO
        #     yield from library.map_impls(impl, key_type, key_func, query_key_func)
    # elif isinstance(plan, plans.Filter):
        # predicate = lambda x: syntax.EBool(True).with_type(syntax.TBool()) # TODO
        # def new_k(elems):
        #     for impl in k(elems):
        #         yield impl.at_query_time(structures.Filtered(elems, predicate))
        # yield from possible_implementations(library, plan.plan, new_k, collection, pseudofields, pseudovars)
        # for impl in possible_implementations(library, plan.plan, library.bag_impls, collection, pseudofields, pseudovars):
        #     yield k(syntax.ECall("Filter", [impl, None]))
    else:
        raise NotImplementedError(plan)
