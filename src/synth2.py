import collections

from z3 import Context, SolverFor

from common import Visitor, fresh_name, split
import predicates
import plans
import syntax
from syntax_tools import free_vars, pprint, subst, alpha_equivalent
import synthesis
import cost_model
import stats
from incrementalization import delta_apply
from typecheck import typecheck

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
Solution = collections.namedtuple("Solution", ["goal", "state", "exp", "ops"])
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
            return syntax.EUnaryOp(op.op, self.visit(op.e))
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

                parts = list(p for p in flatten(op, "and") if p != syntax.EBool(True))
                print(parts)
                if any(p == syntax.EBool(False) for p in parts):
                    return syntax.EBool(False)
                for x in parts:
                    if any(alpha_equivalent(x, syntax.EUnaryOp("not", part)) for part in parts):
                        return syntax.EBool(False)
                if len(parts) == 0: return syntax.EBool(True)
                if len(parts) == 1: return parts[0]
                res = parts[0]
                for i in range(1, len(parts)):
                    res = syntax.EBinOp(res, "and", parts[i])
                return res
            elif op.op == "in":
                e1 = op.e1
                e2 = op.e2
                if isinstance(e2, syntax.EBinOp) and e2.op == "union":
                    lhs = syntax.EBinOp(e1, "in", e2.e1)
                    rhs = syntax.EBinOp(e1, "in", e2.e2)
                    return syntax.EBinOp(lhs, "or", rhs)
                elif isinstance(e2, syntax.EUnaryOp) and e2.op == "singleton":
                    return syntax.EBinOp(e1, "==", e2.e)
            return op
        def visit_EListComprehension(self, lcmp):
            return syntax.EListComprehension(
                self.visit(lcmp.e),
                [self.visit(c) for c in lcmp.clauses])
        def visit_CPull(self, pull):
            return syntax.CPull(pull.id, self.visit(pull.e))
        def visit_CCond(self, cond):
            return syntax.CCond(self.visit(cond.e))
        def visit_Exp(self, e):
            print("*** WARNING: not sure how to simplify {}".format(pprint(e)))
            return e
    return V().visit(e)

@stats.task
def synthesize(state, goals, timeout=None):
    q = collections.deque()
    for g in goals:
        q.append(g)

    solutions = []
    while q:
        print("###### queue len = {}".format(len(q)))
        g = q.popleft()
        e = simplify(g.e)

        for sln in solutions:
            if alpha_equivalent(sln.goal.e, e):
                print("####### already exists: {} as {}".format(e, sln.goal.name))
                e = None
                break

        if e is None:
            continue

        typecheck(e, list(g.args) + list(state))
        print("####### synthesizing: {}({}) = {} = {}".format(g.name, g.args, pprint(g.e), pprint(e)))
        g = g._replace(e=e)
        psoln = synth_simple(state, g, timeout)
        print("####### got: {}".format(psoln))
        solutions.append(psoln.solution)
        for subgoal in psoln.subgoals:
            q.append(subgoal)


    for sln in solutions:
        print("{:10}: {}".format(sln.goal.name, pprint(sln.exp)))
        for name,ty in sln.state:
            print("    {} : {}".format(name, pprint(ty)))


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
        if e.op == "len": agg = Aggregation.Count
        if agg and isinstance(e.e, syntax.EListComprehension):
            pull = find_the_only_pull(e.e)
            pred = combined_predicate(e.e)
            coll = (pull.e.id, statedict[pull.e.id]) if isinstance(pull.e, syntax.EVar) and pull.e.id in statedict else None
            if pull and pred and coll:
                return synthesize_1d(goal, goal.args, agg, e.e.e, pull.id, coll, pred, goal.deltas)
        n = fresh_name()
        fvs = [fv for fv in free_vars(e) if fv.id not in statedict]
        args = [(fv.id, fv.type) for fv in fvs]
        soln = syntax.EUnaryOp(e.op, syntax.ECall(n, [fv for fv in fvs]))
        return PartialSolution(
            solution=Solution(goal, (), syntax.ECall(n, fvs), [syntax.SNoOp() for d in goal.deltas]), # TODO
            subgoals=[Goal(name=n, args=args, e=e.e, deltas=goal.deltas)])
    elif isinstance(e, syntax.ENum):
        return PartialSolution(Solution(goal, (), e, [syntax.SNoOp() for d in goal.deltas]), []) # TODO
    elif isinstance(e, syntax.EListComprehension):
        agg = Aggregation.All
        pull = find_the_only_pull(e)
        pred = combined_predicate(e)
        coll = (pull.e.id, statedict[pull.e.id]) if isinstance(pull.e, syntax.EVar) and pull.e.id in statedict else None
        if pull and pred and coll:
            return synthesize_1d(goal, goal.args, agg, e.e, pull.id, coll, pred, goal.deltas)
        return PartialSolution(
            solution=Solution(goal, (), syntax.ECall("not_implemented", []), [syntax.SNoOp() for d in goal.deltas]), # TODO: for-each loop??
            subgoals=[])
    raise Exception("no idea how to synthesize {}".format(pprint(goal.e)))

@stats.task
def synthesize_1d(goal, input, agg, exp, var, collection, predicate, deltas, timeout=None):
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
        # TODO: agg, plan ----> impl, exp
        state, exp = plan_to_exp(agg, plan, collection[1].t)
        return PartialSolution(Solution(goal, state, exp, op_impls), subgoals)
        # TODO: synthesize ANY of the returned plans??

def plan_to_exp(agg, plan, elem_type):
    if isinstance(plan, plans.AllWhere):
        # I want a collection here: linkedList or ArrayList
        name = fresh_name()
        return ([(name, syntax.TList(elem_type))], syntax.EVar(name))
    elif isinstance(plan, plans.BinarySearch):
        return ([], syntax.ECall("binarysearch", []))
    elif isinstance(plan, plans.HashLookup):
        state, exp = plan_to_exp(agg, plan.plan, elem_type)
        # construct a new type that holds all the state parts
        valueType = syntax.TRecord([(fresh_name(), t) for name, t in state])
        keyType = None
        name = fresh_name()
        compute_key = syntax.EVar(name) # TODO
        lookup = fresh_name()
        return ([(name, syntax.TMap(keyType, valueType))],
            syntax.ELet(
                lookup, syntax.ECall("HashLookup", [syntax.EVar(name), compute_key]),
                subst(exp, { old_name: syntax.EGetField(syntax.EVar(lookup), new_name) for ((old_name, _), (new_name, _)) in zip(state, valueType.fields) })))
    elif isinstance(plan, plans.Concat):
        state1, e1 = plan_to_exp(agg, plan.plan1, elem_type)
        state2, e2 = plan_to_exp(agg, plan.plan2, elem_type)
        if agg == Aggregation.All:
            return (state1 + state2, syntax.ECall("concat", [e1, e2]))
        elif agg == Aggregation.Sum:
            return (state1 + state2, syntax.EBinOp(e1, "+", e2))
        else:
            raise Exception("unhandled case: {}".format(agg))
    elif isinstance(plan, plans.Filter):
        state, e = plan_to_exp(Aggregation.All, plan.plan, elem_type)
        if agg == Aggregation.All:
            return (state, e)
        elif agg == Aggregation.Sum:
            return (state, syntax.ECall("sum", [e]))
        elif agg == Aggregation.Empty:
            return (state, syntax.ECall("is-empty", [e]))
        else:
            raise Exception("unhandled case: {}".format(agg))
    else:
        raise Exception("unhandled case: {}".format(plan))

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
        return (syntax.SNoOp(), [goal1, goal2])

    elif isinstance(plan, plans.Filter):
        return incrementalize(plan.plan, collection, subops, args, member, d)

    elif isinstance(plan, plans.BinarySearch):

        return ("bsinc", []) # TODO

    elif isinstance(plan, plans.HashLookup):

        return ("hashinc", []) # TODO

    elif isinstance(plan, plans.Concat):
        i1, gs1 = incrementalize(plan.plan1, collection, subops, args, member, d)
        i2, gs2 = incrementalize(plan.plan2, collection, subops, args, member, d)
        return (syntax.SSeq(i1, i2), gs1 + gs2)
    else:
        raise Exception("unhandled case: {}".format(plan))
