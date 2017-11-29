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
from cozy.syntax_tools import subst, free_vars, fresh_var, alpha_equivalent, all_exps, BottomUpRewriter, BottomUpExplorer, pprint
from cozy.handle_tools import reachable_handles_at_method
import cozy.incrementalization as inc
from cozy.opts import Option
from cozy.simplification import simplify

from .misc import rewrite_ret, queries_equivalent

dedup_queries = Option("deduplicate-subqueries", bool, True)

def _queries_used_by(thing):
    qs = set()
    class V(BottomUpExplorer):
        def visit_ECall(self, e):
            qs.add(e.func)
    V().visit(thing)
    return qs

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

    def add_query(self, q : Query):
        """
        Given a query in terms of abstract state, add an initial concrete
        implementation.
        """
        self.query_specs.append(q)
        fvs = free_vars(q)
        # initial rep
        qargs = set(EVar(a).with_type(t) for (a, t) in q.args)
        rep = [(fresh_var(v.type), v) for v in fvs if v not in qargs]
        ret = subst(q.ret, { sv.id:v for (v, sv) in rep })
        self.set_impl(q, rep, ret)

    @property
    def op_specs(self):
        return [ m for m in self.spec.methods if isinstance(m, Op) ]

    @property
    def abstract_state(self):
        return [EVar(name).with_type(t) for (name, t) in self.spec.statevars]

    def _add_subquery(self, sub_q : Query, used_by : Stm) -> Stm:
        print("Adding new query {}...".format(sub_q.name))
        # orig_ret = sub_q.ret
        # print("rewritng ret for {}".format(pprint(orig_ret)))
        sub_q = rewrite_ret(sub_q, simplify)
        # if sub_q.ret != orig_ret:
        #     print("rewrote ret")
        #     print(" --> {}".format(pprint(sub_q.ret)))
        qq = find_one(self.query_specs, lambda qq: dedup_queries.value and queries_equivalent(qq, sub_q))
        if qq is not None:
            print("########### subgoal {} is equivalent to {}".format(sub_q.name, qq.name))
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
            handles = reachable_handles_at_method(self.spec, op)
            # print("-"*60)
            for t, bag in handles.items():
                # print("  {} : {}".format(pprint(t), pprint(bag)))
                h = fresh_var(t)
                delta = inc.delta_form(self.spec.statevars + op.args + [(h.id, h.type)], op)
                lval = EGetField(h, "val").with_type(t.value_type)
                new_val = subst(lval, delta)

                # get set of modified handles
                modified_handles = Query(
                    fresh_name("modified_handles"),
                    Visibility.Internal, [], op.assumptions,
                    EFilter(EUnaryOp(UOp.Distinct, bag).with_type(bag.type), ELambda(h, ENot(EEq(lval, new_val)))).with_type(bag.type))
                query_vars = [v for v in free_vars(modified_handles) if v not in self.abstract_state]
                modified_handles.args = [(arg.id, arg.type) for arg in query_vars]

                # modify each one
                (state_update_stm, subqueries) = inc.sketch_update(
                    lval,
                    lval,
                    new_val,
                    self.abstract_state,
                    list(op.assumptions) + [EDeepIn(h, bag), EIn(h, modified_handles.ret)])
                # print("  got {} subqueries".format(len(subqueries)))
                # print("  to update {} in {}, use\n{}".format(pprint(t), op.name, pprint(state_update_stm)))
                for sub_q in subqueries:
                    state_update_stm = self._add_subquery(sub_q=sub_q, used_by=state_update_stm)
                if state_update_stm != SNoOp():
                    state_update_stm = SForEach(h, ECall(modified_handles.name, query_vars).with_type(bag.type), state_update_stm)
                    state_update_stm = self._add_subquery(sub_q=modified_handles, used_by=state_update_stm)
                self.handle_updates[(t, op.name)] = state_update_stm

    def set_impl(self, q : Query, rep : [(EVar, Exp)], ret : Exp):
        to_remove = set()
        for (v, e) in rep:
            aeq = find_one(vv for (vv, ee) in self.concrete_state if alpha_equivalent(e, ee))
            if aeq is not None:
                ret = subst(ret, { v.id : aeq })
                to_remove.add(v)
        rep = [ x for x in rep if x[0] not in to_remove ]

        self.concrete_state.extend(rep)
        self.query_impls[q.name] = rewrite_ret(q, lambda prev: ret, keep_assumptions=False)
        op_deltas = { op.name : inc.delta_form(self.spec.statevars, op) for op in self.op_specs }

        for op in self.op_specs:
            # print("###### INCREMENTALIZING: {}".format(op.name))
            delta = op_deltas[op.name]
            for new_member, projection in rep:
                (state_update_stm, subqueries) = inc.sketch_update(
                    new_member,
                    projection,
                    subst(projection, delta),
                    self.abstract_state,
                    list(op.assumptions))
                for sub_q in subqueries:
                    state_update_stm = self._add_subquery(sub_q=sub_q, used_by=state_update_stm)
                self.updates[(new_member, op.name)] = state_update_stm

    @property
    def code(self) -> Spec:
        # construct new op implementations
        new_ops = []
        for op in self.op_specs:
            stms = [ self.updates[(v, op.name)] for (v, _) in self.concrete_state ]
            stms.extend(hup for ((t, op_name), hup) in self.handle_updates.items() if op.name == op_name)
            new_stms = seq(stms)
            new_ops.append(Op(
                op.name,
                op.args,
                [],
                new_stms))

        # assemble final result
        new_statevars = [(v.id, e.type) for (v, e) in self.concrete_state]
        return Spec(
            self.spec.name,
            self.spec.types,
            self.spec.extern_funcs,
            new_statevars,
            [],
            list(self.query_impls.values()) + new_ops,
            self.spec.header,
            self.spec.footer)

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

        # sort of like mark-and-sweep
        queries_to_keep = OrderedSet(q.name for q in self.query_specs if q.visibility == Visibility.Public)
        state_vars_to_keep = OrderedSet()
        changed = True
        while changed:
            changed = False
            for qname in list(queries_to_keep):
                if qname in self.query_impls:
                    for sv in free_vars(self.query_impls[qname]):
                        if sv not in state_vars_to_keep:
                            state_vars_to_keep.add(sv)
                            changed = True
                    for e in all_exps(self.query_impls[qname].ret):
                        if isinstance(e, ECall):
                            if e.func not in queries_to_keep:
                                queries_to_keep.add(e.func)
                                changed = True
            for op in self.op_specs:
                for ((ht, op_name), code) in self.handle_updates.items():
                    if op.name == op_name:
                        for qname in _queries_used_by(code):
                            if qname not in queries_to_keep:
                                queries_to_keep.add(qname)
                                changed = True

                for sv in state_vars_to_keep:
                    for qname in _queries_used_by(self.updates[(sv, op.name)]):
                        if qname not in queries_to_keep:
                            queries_to_keep.add(qname)
                            changed = True

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
