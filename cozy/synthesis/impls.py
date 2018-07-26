"""
Code relating to implementations.

Implementations are almost exactly like Spec objects, but they have
concretization functions relating them to their underlying specifications and
they store various other information to aid synthesis.
"""

import itertools
from collections import OrderedDict, defaultdict

from cozy.common import fresh_name, find_one, typechecked, OrderedSet
from cozy.syntax import *
from cozy.target_syntax import EFilter, EDeepIn
from cozy.syntax_tools import subst, free_vars, fresh_var, all_exps, BottomUpRewriter, pprint, shallow_copy, unpack_representation, wrap_naked_statevars, rewrite_ret
from cozy.handle_tools import reachable_handles_at_method, implicit_handle_assumptions
import cozy.state_maintenance as inc
from cozy.opts import Option
from cozy.simplification import simplify
from cozy.solver import valid, ModelCachingSolver
from cozy.logging import task, event
from cozy.graph_theory import DirectedGraph

from .misc import queries_equivalent, pull_temps

dedup_queries = Option("deduplicate-subqueries", bool, True)

def simplify_or_ignore(e):
    ee = simplify(e)
    return ee if ee.size() < e.size() else e

class Implementation(object):

    @typechecked
    def __init__(self,
            spec : Spec,
            concrete_state : [(EVar, Exp)],
            query_specs : [Query],
            query_impls : OrderedDict,
            updates : defaultdict,
            handle_updates : defaultdict):
        self.spec = spec
        self.concrete_state = concrete_state
        self.query_specs = query_specs
        self.query_impls = query_impls
        self.updates = updates # maps (concrete_var_name, op_name) to stm
        self.handle_updates = handle_updates # maps (handle_type, op_name) to stm
        self.state_solver = ModelCachingSolver(
            vars=self.abstract_state,
            funcs=self.extern_funcs,
            assumptions=EAll(spec.assumptions))

    def __getstate__(self):
        d = dict(self.__dict__)
        if "state_solver" in d:
            del d["state_solver"]
        if hasattr(self, "__slots__"):
            for a in self.__slots__:
                d[a] = getattr(self, a)
        return d

    def add_query(self, q : Query):
        """
        Given a query in terms of abstract state, add an initial concrete
        implementation.
        """
        print("Adding query {}...".format(q.name))
        self.query_specs.append(q)
        fvs = free_vars(q)
        # initial rep
        qargs = set(EVar(a).with_type(t) for (a, t) in q.args)
        rep, ret = unpack_representation(wrap_naked_statevars(q.ret, self.abstract_state))
        self.set_impl(q, rep, ret)

    @property
    def op_specs(self):
        return [ m for m in self.spec.methods if isinstance(m, Op) ]

    @property
    def abstract_state(self) -> [EVar]:
        return [EVar(name).with_type(t) for (name, t) in self.spec.statevars]

    @property
    def extern_funcs(self) -> { str : TFunc }:
        return OrderedDict((f.name, TFunc(tuple(t for a, t in f.args), f.out_type)) for f in self.spec.extern_funcs)

    def _add_subquery(self, sub_q : Query, used_by : Stm) -> Stm:
        with task("adding query", query=sub_q.name):
            sub_q = shallow_copy(sub_q)
            with task("checking whether we need more handle assumptions"):
                new_a = implicit_handle_assumptions(
                    reachable_handles_at_method(self.spec, sub_q))
                if not valid(EImplies(EAll(sub_q.assumptions), EAll(new_a))):
                    event("we do!")
                    sub_q.assumptions = list(itertools.chain(sub_q.assumptions, new_a))

            with task("repairing state var boundaries"):
                available_state = self.abstract_state + [e for v, e in self.concrete_state]
                sub_q.ret = inc.repair_EStateVar(sub_q.ret, available_state)

            with task("simplifying"):
                orig_a = sub_q.assumptions
                orig_a_size = sum(a.size() for a in sub_q.assumptions)
                orig_ret_size = sub_q.ret.size()
                sub_q.assumptions = tuple(simplify_or_ignore(a) for a in sub_q.assumptions)
                sub_q.ret = simplify(sub_q.ret)
                a_size = sum(a.size() for a in sub_q.assumptions)
                ret_size = sub_q.ret.size()
                event("|assumptions|: {} -> {}".format(orig_a_size, a_size))
                event("|ret|: {} -> {}".format(orig_ret_size, ret_size))

                if a_size > orig_a_size:
                    print("NO, BAD SIMPLIFICATION")
                    print("original")
                    for a in orig_a:
                        print(" - {}".format(pprint(a)))
                    print("simplified")
                    for a in sub_q.assumptions:
                        print(" - {}".format(pprint(a)))
                    assert False

            state_vars = self.abstract_state
            funcs = self.extern_funcs
            qq = find_one(self.query_specs, lambda qq: dedup_queries.value and queries_equivalent(qq, sub_q, state_vars=state_vars, extern_funcs=funcs, assumptions=EAll(self.abstract_invariants)))
            if qq is not None:
                event("subgoal {} is equivalent to {}".format(sub_q.name, qq.name))
                arg_reorder = [[x[0] for x in sub_q.args].index(a) for (a, t) in qq.args]
                class Repl(BottomUpRewriter):
                    def visit_ECall(self, e):
                        args = tuple(self.visit(a) for a in e.args)
                        if e.func == sub_q.name:
                            args = tuple(args[idx] for idx in arg_reorder)
                            return ECall(qq.name, args).with_type(e.type)
                        else:
                            return ECall(e.func, args).with_type(e.type)
                used_by = Repl().visit(used_by)
            else:
                self.add_query(sub_q)
            return used_by

    def _setup_handle_updates(self):
        """
        This method creates update code for handle objects modified by each op.
        Must be called once after all user-specified queries have been added.
        """
        for op in self.op_specs:
            print("Setting up handle updates for {}...".format(op.name))
            handles = reachable_handles_at_method(self.spec, op)
            # print("-"*60)
            for t, bag in handles.items():
                # print("  {} : {}".format(pprint(t), pprint(bag)))
                h = fresh_var(t)
                lval = EGetField(h, "val").with_type(t.value_type)
                new_val = inc.mutate(lval, op.body)

                # get set of modified handles
                modified_handles = Query(
                    fresh_name("modified_handles"),
                    Visibility.Internal, [], op.assumptions,
                    EFilter(EUnaryOp(UOp.Distinct, bag).with_type(bag.type), ELambda(h, ENot(EEq(lval, new_val)))).with_type(bag.type),
                    "[{}] modified handles of type {}".format(op.name, pprint(t)))
                query_vars = [v for v in free_vars(modified_handles) if v not in self.abstract_state]
                modified_handles.args = [(arg.id, arg.type) for arg in query_vars]

                # modify each one
                subqueries = []
                state_update_stm = inc.mutate_in_place(
                    lval,
                    lval,
                    op.body,
                    abstract_state=self.abstract_state,
                    assumptions=list(op.assumptions) + [EDeepIn(h, bag), EIn(h, modified_handles.ret)],
                    invariants=self.abstract_invariants,
                    subgoals_out=subqueries)
                for sub_q in subqueries:
                    sub_q.docstring = "[{}] {}".format(op.name, sub_q.docstring)
                    state_update_stm = self._add_subquery(sub_q=sub_q, used_by=state_update_stm)
                if state_update_stm != SNoOp():
                    state_update_stm = SForEach(h, ECall(modified_handles.name, query_vars).with_type(bag.type), state_update_stm)
                    state_update_stm = self._add_subquery(sub_q=modified_handles, used_by=state_update_stm)
                self.handle_updates[(t, op.name)] = state_update_stm

    def set_impl(self, q : Query, rep : [(EVar, Exp)], ret : Exp):
        with task("updating implementation", query=q.name):
            with task("finding duplicated state vars"):
                to_remove = set()
                for (v, e) in rep:
                    aeq = find_one(vv for (vv, ee) in self.concrete_state if e.type == ee.type and self.state_solver.valid(EEq(e, ee)))
                    # aeq = find_one(vv for (vv, ee) in self.concrete_state if e.type == ee.type and alpha_equivalent(e, ee))
                    if aeq is not None:
                        event("state var {} is equivalent to {}".format(v.id, aeq.id))
                        ret = subst(ret, { v.id : aeq })
                        to_remove.add(v)
                rep = [ x for x in rep if x[0] not in to_remove ]

            self.concrete_state.extend(rep)
            self.query_impls[q.name] = rewrite_ret(q, lambda prev: ret, keep_assumptions=False)

            for op in self.op_specs:
                with task("incrementalizing query", query=q.name, op=op.name):
                    for new_member, projection in rep:
                        subqueries = []
                        state_update_stm = inc.mutate_in_place(
                            new_member,
                            projection,
                            op.body,
                            abstract_state=self.abstract_state,
                            assumptions=op.assumptions,
                            invariants=self.abstract_invariants,
                            subgoals_out=subqueries)
                        for sub_q in subqueries:
                            sub_q.docstring = "[{}] {}".format(op.name, sub_q.docstring)
                            state_update_stm = self._add_subquery(sub_q=sub_q, used_by=state_update_stm)
                        self.updates[(new_member, op.name)] = state_update_stm

    @property
    def code(self) -> Spec:

        state_read_by_query = {
            query_name : free_vars(query)
            for query_name, query in self.query_impls.items() }

        # prevent read-after-write by lifting reads before writes.

        # list of SDecls
        temps = defaultdict(list)
        updates = dict(self.updates)

        concrete_state_vars = [v for v, e in self.concrete_state]

        for operator in self.op_specs:

            # Compute order constraints between statements:
            #   v1 -> v2 means that the update code for v1 should (if possible)
            #   appear before the update code for v2
            #   (i.e. the update code for v1 reads v2)
            def state_used_during_update(v1 : EVar) -> [EVar]:
                v1_update_code = self.updates[(v1, operator.name)]
                v1_queries = list(self.queries_used_by(v1_update_code))
                res = OrderedSet()
                for q in v1_queries:
                    res |= state_read_by_query[q]
                return res
            g = DirectedGraph(
                nodes=concrete_state_vars,
                successors=state_used_during_update)

            # Find the minimum set of edges we need to break cycles (see
            # "feedback arc set problem")
            edges_to_break = g.minimum_feedback_arc_set()
            g.delete_edges(edges_to_break)
            ordered_concrete_state = list(g.toposort())

            # Lift auxiliary declarations as needed
            things_updated = []
            for v in ordered_concrete_state:
                things_updated.append(v)
                stm = updates[(v, operator.name)]
                def problematic(e):
                    for x in all_exps(e):
                        if isinstance(x, ECall) and x.func in [q.name for q in self.query_specs]:
                            problems = set(things_updated) & state_read_by_query[x.func]
                            if problems:
                                return True
                    return False
                stm = pull_temps(stm,
                    decls_out=temps[operator.name],
                    exp_is_bad=problematic)
                updates[(v, operator.name)] = stm

        # construct new op implementations
        new_ops = []
        for op in self.op_specs:

            stms = [ updates[(v, op.name)] for v in ordered_concrete_state ]
            stms.extend(hup for ((t, op_name), hup) in self.handle_updates.items() if op.name == op_name)
            new_stms = seq(temps[op.name] + stms)
            new_ops.append(Op(
                op.name,
                op.args,
                [],
                new_stms,
                op.docstring))

        # assemble final result
        return Spec(
            self.spec.name,
            self.spec.types,
            self.spec.extern_funcs,
            [(v.id, e.type) for (v, e) in self.concrete_state],
            [],
            list(self.query_impls.values()) + new_ops,
            self.spec.header,
            self.spec.footer,
            self.spec.docstring)

    @property
    def abstract_invariants(self) -> [Exp]:
        return list(self.spec.assumptions)

    @property
    def concretization_functions(self) -> { str : Exp }:
        state_var_exps = OrderedDict()
        for (v, e) in self.concrete_state:
            state_var_exps[v.id] = e
        return state_var_exps

    def cleanup(self):
        """
        Remove unused state, queries, and updates.
        """

        def deps(thing):
            if isinstance(thing, str):
                yield from free_vars(self.query_impls[thing])
            elif isinstance(thing, EVar):
                for op in self.op_specs:
                    yield self.updates[(thing, op.name)]
            elif isinstance(thing, Stm):
                yield from self.queries_used_by(thing)
            else:
                raise ValueError(repr(thing))

        g = DirectedGraph(
            nodes=itertools.chain(self.query_impls.keys(), (v for v, _ in self.concrete_state), self.updates.values()),
            successors=deps)
        roots = [q.name for q in self.query_specs if q.visibility == Visibility.Public]
        roots.extend(itertools.chain(*[self.queries_used_by(code) for ((ht, op_name), code) in self.handle_updates.items()]))
        queries_to_keep = set(q for q in g.reachable_nodes(roots) if isinstance(q, str))

        # remove old specs
        for q in list(self.query_specs):
            if q.name not in queries_to_keep:
                self.query_specs.remove(q)

        # remove old implementations
        for qname in list(self.query_impls.keys()):
            if qname not in queries_to_keep:
                del self.query_impls[qname]

        # remove old state vars
        self.concrete_state = [ v for v in self.concrete_state if any(v[0] in free_vars(q) for q in self.query_impls.values()) ]

        # remove old method implementations
        for k in list(self.updates.keys()):
            v, op_name = k
            if v not in [var for (var, exp) in self.concrete_state]:
                del self.updates[k]

    def queries_used_by(self, stm):
        for e in all_exps(stm):
            if isinstance(e, ECall) and e.func in [q.name for q in self.query_specs]:
                yield e.func

    def states_maintained_by(self, q : Query) -> [EVar]:
        concrete_vars = []
        for (var_name, op_name), stm in self.updates.items():
            if q.name in self.queries_used_by(stm):
                concrete_vars.append(var_name)
        return concrete_vars

@typechecked
def construct_initial_implementation(spec : Spec) -> Implementation:
    """
    Takes a typechecked specification as input, returns an initial
    implementation.
    """

    impl = Implementation(spec, [], [], OrderedDict(), defaultdict(SNoOp), defaultdict(SNoOp))
    for m in spec.methods:
        if isinstance(m, Query):
            impl.add_query(m)
    impl._setup_handle_updates()
    impl.cleanup()

    # print(pprint(impl.code))
    # raise NotImplementedError()

    return impl
