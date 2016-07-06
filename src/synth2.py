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
from typecheck import typecheck
import incrementalization as inc
import aggregations
import library

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

        def splitoff(self, e, as_bool=True):
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
            # if e.type == syntax.TBool():
            #     true = syntax.EBool(True)
            #     if true in mapping:
            #         b = mapping[true][0]
            #     else:
            #         b = fresh_name()
            #         res = (b, (), syntax.EBool(True))
            #         self.pseudovars.append(res)
            #         mapping[true] = res
            #     return predicates.Compare(predicates.Var(n), predicates.Eq, predicates.Var(b))
            # else:
            #     return predicates.Var(n)
            return predicates.Var(n)

        def visit_Exp(self, e, as_bool=True):
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

        for sln in solutions:
            if alpha_equivalent(sln.goal.e, e):
                print("####### already exists: {} as {}".format(e, sln.goal.name))
                e = None
                break

        if e is None:
            solutions.append(Solution(goal=g, state=(), exp=sln.exp, ops=[syntax.SNoOp() for d in ds]))
            continue

        typecheck(e, list(g.args) + list(state))
        print("####### synthesizing: {}({}) = {} = {}".format(g.name, g.args, pprint(g.e), pprint(e)))
        g = g._replace(e=e)
        psoln = synth_simple(context, g, timeout)
        print("####### got: {}".format(psoln))
        solutions.append(psoln.solution)
        for subgoal in psoln.subgoals:
            q.append(subgoal)


    for sln in solutions:
        print("{:10}: {}".format(sln.goal.name, pprint(sln.exp)))
        for name,ty in sln.state:
            print("    {} : {}".format(name, pprint(ty)))

    print(solutions)
    return syntax.Spec(
        spec.name,
        spec.types,
        [v for sln in solutions for v in sln.state],
        (),
        [syntax.Op(ops[i].name, ops[i].args, (), syntax.seq([sln.ops[i] for sln in solutions])) for i in range(len(ops))] +
        [syntax.Query(sln.goal.name, sln.goal.args, (), sln.exp) for sln in solutions])

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
def synth_simple(context, goal, timeout=None):
    statedict = dict(context.state)
    deltas = context.deltas
    no_delta = [syntax.SNoOp() for d in deltas]
    e = goal.e
    if isinstance(e, syntax.EUnaryOp):
        if isinstance(e.e, syntax.EListComprehension):

            pull = find_the_only_pull(e.e)
            if pull:
                if e.op == "iterator":   agg = aggregations.IterateOver(lambda x: subst(e.e.e, { pull.id: x }))
                elif e.op == "sum":      agg = aggregations.Sum(lambda x: subst(e.e.e, { pull.id: x }))
                elif e.op == "min":      agg = aggregations.Min(lambda x: x)
                elif e.op == "max":      agg = aggregations.Max(lambda x: x)
                elif e.op == "distinct": agg = aggregations.DistinctElements()
                else: raise NotImplementedError(e.op)

                pred = combined_predicate(e.e)
                coll = (pull.e.id, statedict[pull.e.id]) if isinstance(pull.e, syntax.EVar) and pull.e.id in statedict else None
                if pred and coll:
                    return synthesize_1d(goal, goal.args, agg, e.e.e, pull.id, coll, pred, deltas)

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
            return synth_simple(context, Goal(name=goal.name, args=goal.args, e=syntax.EUnaryOp(e.op, syntax.EListComprehension(syntax.EVar(n), [syntax.CPull(n, e.e)]))), timeout)
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
            return synthesize_1d(goal, (), aggregations.IterateOver(lambda x: x), syntax.EVar(n), n, (e.id, statedict[e.id]), syntax.EBool(True), deltas)
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
            solution=Solution(goal, (), syntax.ECall(g.name, [syntax.EVar(v) for v,t in g.args]), no_delta),
            subgoals=[g])
    elif isinstance(e, syntax.EGetField):
        g = Goal(
            name=fresh_name(),
            args=goal.args,
            e=e.e)
        return PartialSolution(
            solution=Solution(goal, (), syntax.EGetField(syntax.ECall(g.name, [syntax.EVar(a) for a,t in goal.args]), e.f), no_delta),
            subgoals=[g])

    # return PartialSolution(
    #     solution=Solution(goal, (), syntax.ECall("not_implemented", [e]), [syntax.SNoOp() for d in deltas]), # TODO: for-each loop??
    #     subgoals=[])
    # raise NotImplementedError("no idea how to synthesize {}".format(pprint(goal.e)))
    print("WARNING: no idea how to synthesize {}".format(pprint(goal.e)))
    return PartialSolution(
        solution=Solution(goal, (), goal.e, no_delta),
        subgoals=())

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
        agg         - an Aggregation
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

    print("Calling Cozy on {} ----> {}".format(pprint(predicate), abstraction))

    # TODO: try all?
    for plan in ctx.synthesizePlansByEnumeration(abstraction, sort_field=None, timeout=timeout):
        subgoals = [Goal(name, args, e) for (name, args, e) in pseudofields + pseudovars + subops]
        # print(plan)

        # TODO: try all?
        new_state_name = fresh_name()
        for proj, get in understand_plan(agg, plan, collection, new_state_name):
            print((proj, get))

            op_impls = []
            for (name, args, member, d) in deltas:
                (op_impl, op_subgoals) = proj.incrementalize(syntax.EVar(new_state_name), collection[0], d)
                op_impls.append(op_impl)
                for sg in op_subgoals:
                    sg = Goal(sg.name, args, sg.e)
                    subgoals.append(sg)

            new_type = proj.result_type()
            return PartialSolution(Solution(goal, [(new_state_name, new_type)], get, op_impls), subgoals)
            # TODO: synthesize ANY of the returned plans??

        raise Exception("no understanding for {}".format(plan))
    raise Exception("no plan for {}".format(abstraction))

class StateProjection(object):
    def incrementalize(self, target, var, delta):
        """
        Update `target` when delta `d` is applied to `var`.
        Returns (impl, subgoals).
        """
        raise NotImplementedError()
    def result_type(self):
        """
        The result type of performing this projection.
        """
        raise NotImplementedError()
    def abstract_state(self):
        """
        The abstract state that this projection tracks.
        Returns (state_var_name, type)
        """
        raise NotImplementedError()

class ToLinkedList(StateProjection):
    def __init__(self, e, elem_proj=lambda x: x):
        self.e = e
    def incrementalize(self, target, var, delta):
        d = inc.change_to(self.e, var, delta)
        if isinstance(d, inc.NoDelta):
            return (syntax.SNoOp(), ())
        elif isinstance(d, inc.SetAdd) or isinstance(d, inc.ListAddFront):
            return (syntax.SCall(target, "linkedlist-insert-front", [d.e]), ())
        elif isinstance(d, inc.ListAddBack):
            return (syntax.SCall(target, "linkedlist-insert-back", [d.e]), ())
        elif isinstance(d, inc.SetRemove):
            return (syntax.SCall(target, "linkedlist-remove", [d.e]), ())
        else:
            raise NotImplementedError(d)
    def result_type(self):
        return library.LinkedList()

class ToHashSet(StateProjection):
    def __init__(self, e, elem_proj=lambda x: x):
        self.e = e
    def incrementalize(self, target, var, delta):
        d = inc.change_to(self.e, var, delta)
        raise NotImplementedError(d)
    def result_type(self):
        return library.HashSet()

class TrackSum(StateProjection):
    def __init__(self, e, elem_proj=lambda x: x):
        self.e = e
        self.elem_proj = elem_proj
    def incrementalize(self, target, var, delta):
        d = inc.change_to(self.e, var, delta)
        if isinstance(d, inc.NoDelta):
            return (syntax.SNoOp(), ())
        elif isinstance(d, inc.SetAdd) or isinstance(d, inc.ListAddBack) or isinstance(d, inc.ListAddFront):
            return (syntax.SAssign(target, syntax.EBinOp(target, "+", self.elem_proj(d.e))), ())
        elif isinstance(d, inc.SetRemove) or isinstance(d, inc.ListRemove):
            return (syntax.SAssign(target, syntax.EBinOp(target, "-", self.elem_proj(d.e))), ())
        else:
            raise NotImplementedError(d)
    def result_type(self):
        return syntax.TInt() # TODO

class TrackMin(StateProjection):
    def __init__(self, e, key_func=lambda x: x):
        self.e = e
        self.key_func = key_func
    def incrementalize(self, target, var, delta):
        d = inc.change_to(self.e, var, delta)
        if isinstance(d, inc.NoDelta):
            return (syntax.SNoOp(), ())
        elif isinstance(d, inc.SetAdd):
            return (syntax.SIf(syntax.EBinOp(self.key_func(d.e), "<", self.key_func(target)),
                syntax.SAssign(target, d.e),
                syntax.SNoOp()), ())
        else:
            raise NotImplementedError(d)
    def result_type(self):
        return syntax.TInt() # TODO

class ToHashMap(StateProjection):
    def __init__(self, abstract_collection, key_func, sub_projection):
        self.abstract_collection = abstract_collection
        self.key_func = key_func
        self.sub_projection = sub_projection
    def incrementalize(self, target, var, delta):
        k = fresh_name()
        e = fresh_name()
        # affected_keys = Goal(
        #     name=fresh_name(),
        #     args=(), # TODO
        #     # e = distinct [k | k <- [key(e) | e <- elems], val(k) != val'(k)]
        #     e=syntax.EUnaryOp("distinct",
        #         syntax.EListComprehension(syntax.EVar(k), [
        #             syntax.CPull(k, syntax.EListComprehension(self.key_func(syntax.EVar(e)), [syntax.CPull(e, syntax.EVar(self.abstract_collection[0]))])),
        #             syntax.CCond(syntax.EBinOp(syntax.EBool(True), "!=", syntax.EBool(True)))]))) # TODO
        # x = fresh_name()
        # return (syntax.SForEach(x, syntax.ECall(affected_keys.name, []), self.sub_projection.incrementalize(syntax.ECall("hash-find", [target, syntax.EVar(x)]), var, delta)), [affected_keys])
        affected_keys = syntax.EVar(k)
        x = fresh_name()
        subop, subgoals = self.sub_projection.incrementalize(syntax.ECall("hash-find", [target, syntax.EVar(x)]), var, delta)
        return (syntax.SForEach(x, affected_keys, subop), subgoals)
    def result_type(self):
        return self.sub_projection.result_type()
    def abstract_state(self):
        return self.abstract_collection

def understand_plan(agg, plan, collection, name):
    """
    Args:
        agg        - an Aggregation
        plan       - a Plan
        collection - (name, syntax.Type)
    Generates tuples
        (proj, get)
    where
        proj - a StateProjection from abstract state to concrete state
        get  - a program to compute the plan result for the given agg over (name, type)
    """
    if isinstance(plan, plans.AllWhere):
        guard = predicate_to_exp(plan.toPredicate())
        # TODO: handle guard
        if isinstance(agg, aggregations.IterateOver):
            yield (ToLinkedList(syntax.EVar(collection[0])), syntax.ECall("iterator", [syntax.EVar(name)]))
        if isinstance(agg, aggregations.DistinctElements):
            yield (ToHashSet(syntax.EVar(collection[0])), syntax.EVar(name))
        elif isinstance(agg, aggregations.Sum):
            yield (TrackSum(syntax.EVar(collection[0]), agg.projection), syntax.EVar(name))
        elif isinstance(agg, aggregations.Min):
            yield (TrackMin(syntax.EVar(collection[0]), agg.key_func), syntax.EVar(name))
        elif isinstance(agg, aggregations.GroupBy):
            sub_name = fresh_name()
            v = fresh_name()
            for (sub_proj, sub_get) in understand_plan(agg.sub_agg, plan, (sub_name, collection[1]), v):
                yield (ToHashMap(collection, agg.key_func, sub_proj), syntax.ELet(v, syntax.ECall("hash-lookup", [syntax.EVar(name)]), sub_get))
        else:
            raise NotImplementedError(agg)
    elif isinstance(plan, plans.HashLookup):
        f = lambda e: e # TODO
        agg = aggregations.GroupBy(f, agg)
        yield from understand_plan(agg, plan.plan, collection, name)
    else:
        raise NotImplementedError(plan)
