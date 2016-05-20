import collections

from z3 import Context, SolverFor

from common import Visitor, fresh_name, split
import predicates
import plans
import syntax
from syntax_tools import free_vars, pprint, subst
import synthesis
import cost_model
import stats
from incrementalization import delta_apply

class Aggregation(object):
    All      = "All"
    Distinct = "Distinct"
    AnyElt   = "AnyElt"
    Min      = "Min"
    Max      = "Max"
    Count    = "Count"
    Sum      = "Sum"
    Empty    = "Empty"

Goal = collections.namedtuple("Goal", ["name", "args", "e", "deltas"])
Solution = collections.namedtuple("Solution", ["agg", "plan", "ops"])
PartialSolution = collections.namedtuple("PartialSolution", ["solution", "subgoals"])

def abstractify(input, var, predicate):

    class V(Visitor):
        def __init__(self):
            self.pseudofields = []
            self.pseudovars = []
            self.subops = []

        def visit_EBool(self, e):
            return predicates.Bool(e.val)

        def visit_EBinOp(self, e):
            if e.op == "and":
                return predicates.And(self.visit(e.e1), self.visit(e.e2))
            if e.op == "or":
                return predicates.Or(self.visit(e.e1), self.visit(e.e2))
            if e.op in [">", ">=", "<", "<=", "==", "!="]:
                if e.op == ">":  op = predicates.Gt
                if e.op == ">=": op = predicates.Ge
                if e.op == "<":  op = predicates.Lt
                if e.op == "<=": op = predicates.Le
                if e.op == "==": op = predicates.Eq
                if e.op == "!=": op = predicates.Ne
                return predicates.Compare(self.visit(e.e1), op, self.visit(e.e2))
            return self.splitoff(e)

        def visit_EUnaryOp(self, e):
            if e.op == "not":
                return predicates.Not(self.visit(e.e))
            return self.splitoff(e)

        def splitoff(self, e):
            args = [v for v in free_vars(e) if v.id == var or v.id in [i[0] for i in input]]
            fvs = {v.id for v in args}
            argtypes = [(arg.id, arg.type) for arg in args]
            n = fresh_name()
            if fvs == {var} or not fvs:
                self.pseudofields.append((n, argtypes, e))
            elif var not in fvs:
                self.pseudovars.append((n, argtypes, e))
            else:
                self.subops.append((n, argtypes, e))
            if e.type == syntax.TBool():
                return predicates.Compare(predicates.Var(n), predicates.Eq, predicates.Bool(True))
            else:
                return predicates.Var(n)

        def visit_Exp(self, e):
            return self.splitoff(e)

    v = V()
    p = v.visit(predicate)
    return (v.pseudofields, v.pseudovars, v.subops, p)

def predicate_to_exp(p):
    class V(Visitor):
        def visit_Bool(self, b):
            return syntax.EBool(b.val)
        def visit_Compare(self, cmp):
            if cmp.op == predicates.Gt: op = ">"
            if cmp.op == predicates.Ge: op = ">="
            if cmp.op == predicates.Lt: op = "<"
            if cmp.op == predicates.Le: op = "<="
            if cmp.op == predicates.Eq: op = "=="
            if cmp.op == predicates.Ne: op = "!="
            return syntax.EBinOp(self.visit(cmp.lhs), op, self.visit(cmp.rhs))
        def visit_Var(self, v):
            return syntax.EVar(v.name)
    v = V()
    cond = v.visit(p)
    return cond

@stats.task
def synthesize(state, goals, timeout=None):
    q = collections.deque()
    for g in goals:
        q.append(g)

    solutions = []
    while q:
        g = q.popleft()
        print("####### synthesizing: {}({}) = {}".format(g.name, g.args, pprint(g.e)))
        psoln = synth_simple(state, g, timeout)
        print("####### got: {}".format(psoln))
        solutions.append(psoln.solution)
        for subgoal in psoln.subgoals:
            q.append(subgoal)

    return solutions

def combined_predicate(lcmp):
    l = syntax.EBool(True)
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

@stats.task
def synth_simple(state, goal, timeout=None):
    statedict = dict(state)
    e = goal.e
    if isinstance(e, syntax.EUnaryOp):
        agg = None
        if e.op == "some": agg = Aggregation.AnyElt
        if e.op == "empty": agg = Aggregation.Empty
        if agg and isinstance(e.e, syntax.EListComprehension):
            pull = find_the_only_pull(e.e)
            pred = combined_predicate(e.e)
            coll = (pull.e.id, statedict[pull.e.id]) if isinstance(pull.e, syntax.EVar) and pull.e.id in statedict else None
            if pull and pred and coll:
                return synthesize_1d(goal.args, agg, e.e.e, pull.id, coll, pred, goal.deltas)
        n = fresh_name()
        fvs = [fv for fv in free_vars(e) if fv.id not in statedict]
        args = [(fv.id, fv.type) for fv in fvs]
        soln = syntax.EUnaryOp(e.op, syntax.ECall(n, [fv for fv in fvs]))
        return PartialSolution(
            solution=Solution(None, None, None), # TODO
            subgoals=[Goal(name=n, args=args, e=e.e, deltas=goal.deltas)])
    elif isinstance(e, syntax.ENum):
        return PartialSolution(Solution(None, None, None), []) # TODO
    raise Exception("no idea how to synthesize {}".format(pprint(goal.e)))

@stats.task
def synthesize_1d(input, agg, exp, var, collection, predicate, deltas, timeout=None):
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
        agg         - one of Aggregation.{All,Sum,...}
        exp         - Exp representing e
        var         - id of v
        collection  - (L, Type of L)
        predicate   - Exp representing P
        deltas      - list of modification ops to abstract state

    This function returns the best outline found in the given timeout, or the
    optimal outline if timeout is None. The outline has the form

        (n, T, g, d, s)

    where
        n,T     is a new name and type for the abstract state
        g       is a new implementation of f over n and T
        d       is a list of change implementations, one for each delta
        s       is a set of sub-ops that must also be solved
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
    ctx = synthesis.SolverContext(
        varNames=vnames,
        fieldNames=fnames,
        cost_model=lambda plan: cost_model.cost(None, None, plan))
    for plan in ctx.synthesizePlansByEnumeration(abstraction, sort_field=None, timeout=timeout):
        subgoals = [Goal(name, args, e, deltas) for (name, args, e) in pseudofields + pseudovars + subops]
        # print(plan)

        op_impls = []
        for (name, args, member, d) in deltas:
            (op_impl, op_subgoals) = incrementalize(plan, collection, pseudofields + pseudovars + subops, args, member, d)
            op_impls.append((name, op_impl))
            for sg in op_subgoals:
                sg = Goal(sg.name, args, sg.e, deltas)
                subgoals.append(sg)
        # print(op_impls)
        # for sg in subgoals:
        #     print("subgoal: {}({}) = {}".format(sg.name, sg.args, pprint(sg.e)))
        return PartialSolution(Solution(agg, plan, op_impls), subgoals)
        # TODO: synthesize ANY of the returned plans??

def incrementalize(plan, collection, subops, args, member, d):
    if isinstance(plan, plans.AllWhere):

        # reconstruct expression
        cond = predicate_to_exp(plan.toPredicate())
        # cond = subst(cond, { name : syntax.ECall(name, [syntax.EVar(v) for (v, t) in args]) for (name, args, e) in pseudofields + pseudovars + subops })
        cond = subst(cond, { name : e for (name, args, e) in subops })
        newcond = delta_apply(cond, args, member, d)
        var = fresh_name()
        # lcmp = syntax.EListComprehension(syntax.EVar(var), [syntax.CPull(var, syntax.EVar(collection[0])), syntax.CCond(cond)])
        # print(pprint(lcmp))
        # print(pprint(cond))

        g1name = fresh_name()
        goal1 = Goal(g1name, None, syntax.EListComprehension(syntax.EVar(var), [syntax.CPull(var, syntax.EVar(collection[0])), syntax.CCond(syntax.EBinOp(cond, "and", syntax.EUnaryOp("not", newcond)))]), None)

        g2name = fresh_name()
        goal2 = Goal(g2name, None, syntax.EListComprehension(syntax.EVar(var), [syntax.CPull(var, syntax.EVar(collection[0])), syntax.CCond(syntax.EBinOp(syntax.EUnaryOp("not", cond), "and", newcond))]), None)
        return (None, [goal1, goal2])

    elif isinstance(plan, plans.Filter):
        return incrementalize(plan.plan, collection, subops, args, member, d)
    else:
        raise Exception("unhandled case: {}".format(plan))
