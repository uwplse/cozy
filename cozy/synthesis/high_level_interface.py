from collections import namedtuple, deque, defaultdict
import datetime
import itertools

from cozy.common import typechecked, fresh_name, mk_map, pick_to_sum, nested_dict
from cozy.target_syntax import *
import cozy.syntax_tools
from cozy.syntax_tools import all_types, alpha_equivalent, BottomUpExplorer, BottomUpRewriter, free_vars, pprint, subst, implies, fresh_var, mk_lambda, all_exps, equal
import cozy.incrementalization as inc
from cozy.typecheck import INT, BOOL
from cozy.timeouts import Timeout, TimeoutException
from cozy.cost_model import CompositeCostModel
from cozy.rep_inference import infer_rep
from cozy import jobs

from . import core
from . import caching

SynthCtx = namedtuple("SynthCtx", ["all_types", "basic_types"])

def rename_args(queries : [Query]) -> [Query]:
    arg_hist = mk_map((a for q in queries for (a, t) in q.args), v=len)
    res = []
    for q in queries:
        arg_remap = { a : EVar(fresh_name(a)).with_type(t) for (a, t) in q.args if arg_hist[a] > 1 }
        if arg_remap:
            q = Query(
                q.name,
                tuple((arg_remap.get(a, EVar(a)).id, t) for (a, t) in q.args),
                subst(q.assumptions, arg_remap),
                subst(q.ret, arg_remap))
        res.append(q)
    return res

def _as_conjunction_of_equalities(p):
    if isinstance(p, EBinOp) and p.op == "and":
        return _as_conjunction_of_equalities(p.e1) + _as_conjunction_of_equalities(p.e2)
    elif isinstance(p, EBinOp) and p.op == "==":
        return [p]
    else:
        raise ValueError(p)

def as_conjunction_of_equalities(p):
    try:
        return _as_conjunction_of_equalities(p)
    except ValueError:
        return None

def infer_key_and_value(filter, binders, state : {EVar} = set()):
    equalities = as_conjunction_of_equalities(filter)
    if not equalities:
        return
    def can_serve_as_key(e, binder):
        fvs = free_vars(e)
        return binder in fvs and all(v == binder or v in state for v in fvs)
    def can_serve_as_value(e, binder):
        fvs = free_vars(e)
        return binder not in fvs and not all(v in state for v in fvs)
    for b in binders:
        sep = []
        for eq in equalities:
            if can_serve_as_key(eq.e1, b) and can_serve_as_value(eq.e2, b):
                sep.append((eq.e1, eq.e2))
            elif can_serve_as_key(eq.e2, b) and can_serve_as_value(eq.e1, b):
                sep.append((eq.e2, eq.e1))
        if len(sep) == len(equalities):
            key = ETuple(tuple(k for k, v in sep)).with_type(TTuple(tuple(k.type for k, v in sep))) if len(sep) > 1 else sep[0][0]
            val = ETuple(tuple(v for k, v in sep)).with_type(TTuple(tuple(v.type for k, v in sep))) if len(sep) > 1 else sep[0][1]
            yield b, key, val

class BinderBuilder(core.ExpBuilder):
    def __init__(self, binders, state_vars : [EVar], roots):
        super().__init__()
        self.binders = binders
        self.state_vars = state_vars
        self.roots = roots
    def build(self, cache, size):
        if size == 1:
            # print("Roots:")
            # for r in self.roots:
            #     print("    {} : {}".format(pprint(r), pprint(r.type)))
            # print()
            yield EBool(True).with_type(BOOL)
            yield EBool(False).with_type(BOOL)
            yield from self.roots
            yield from (b for b in self.binders if b not in self.roots)
            return

        # print("Cache:")
        # for (e, size) in cache:
        #     print("    @{}\t:\t{}".format(size, pprint(e)))

        for e in cache.find(type=TRecord, size=size-1):
            for (f,t) in e.type.fields:
                yield EGetField(e, f).with_type(t)
        for e in itertools.chain(cache.find(type=TBag(INT), size=size-1), cache.find(type=TSet(INT), size=size-1)):
            yield EUnaryOp("sum", e).with_type(INT)
        for e in cache.find(type=TBag, size=size-1):
            yield EUnaryOp("the", e).with_type(TMaybe(e.type.t))
        for e in cache.find(type=THandle, size=size-1):
            yield EGetField(e, "val").with_type(e.type.value_type)
        for e in cache.find(type=TTuple, size=size-1):
            for n in range(len(e.type.ts)):
                yield ETupleGet(e, n).with_type(e.type.ts[n])
        for e in cache.find(type=BOOL, size=size-1):
            yield EUnaryOp("not", e).with_type(BOOL)

        for (sz1, sz2) in pick_to_sum(2, size - 1):
            # Try instantiating bound expressions
            for e1 in cache.find(size=sz1):
                binders = free_vars(e1) & set(self.binders)
                for b in binders:
                    for e2 in cache.find(type=b.type, size=sz2):
                        e = subst(e1, { b.id: e2 })
                        e._tag = True
                        yield e
            for a1 in cache.find(type=INT, size=sz1):
                for a2 in cache.find(type=INT, size=sz2):
                    # yield EBinOp(a1, "+", a2).with_type(INT)
                    # yield EBinOp(a1, "-", a2).with_type(INT)
                    yield EBinOp(a1, ">", a2).with_type(BOOL)
                    yield EBinOp(a1, "<", a2).with_type(BOOL)
                    yield EBinOp(a1, ">=", a2).with_type(BOOL)
                    yield EBinOp(a1, "<=", a2).with_type(BOOL)
            for a1 in cache.find(type=TBag, size=sz1):
                if not isinstance(a1.type.t, THandle):
                    continue
                for a2 in cache.find(type=a1.type, size=sz2):
                    yield EBinOp(a1, "+", a2).with_type(a1.type)
            for a1 in cache.find(type=BOOL, size=sz1):
                for a2 in cache.find(type=BOOL, size=sz2):
                    yield EBinOp(a1, "and", a2).with_type(BOOL)
                    yield EBinOp(a1, "or", a2).with_type(BOOL)
            for a1 in cache.find(size=sz1):
                if not isinstance(a1.type, TMap):
                    for a2 in cache.find(type=a1.type, size=sz2):
                        yield EBinOp(a1, "==", a2).with_type(BOOL)
            for m in cache.find(type=TMap, size=sz1):
                for k in cache.find(type=m.type.k, size=sz2):
                    yield EMapGet(m, k).with_type(m.type.v)

        for bag in itertools.chain(cache.find(type=TBag, size=size-1), cache.find(type=TSet, size=size-1)):
            if not isinstance(bag.type.t, THandle):
                continue

            # len of bag
            count = EUnaryOp("sum", EMap(bag, mk_lambda(bag.type.t, lambda x: ENum(1).with_type(INT))).with_type(TBag(INT))).with_type(INT)
            yield count
            # empty?
            empty = EBinOp(count, "==", ENum(0).with_type(INT)).with_type(BOOL)
            yield empty
            # exists?
            yield ENot(empty)

            # construct map lookups
            if isinstance(bag, EFilter):
                binder = bag.p.arg
                found = False
                for (_, key_proj, key_lookup) in infer_key_and_value(bag.p.body, [binder], state=set(self.state_vars)):
                    # print("for {}: {} {} {}".format(pprint(bag.p.body), pprint(bag), pprint(key_proj), pprint(key_lookup)))
                    found = True
                    yield EMapGet(
                        EMakeMap(
                            bag.e,
                            ELambda(binder, key_proj),
                            mk_lambda(bag.type, lambda xs: xs)).with_type(TMap(key_proj.type, bag.type)),
                        key_lookup).with_type(bag.type)
                # if not found:
                #     print("DUD FIND: {}".format(pprint(bag)))

        for (sz1, sz2) in pick_to_sum(2, size - 1):
            for bag in itertools.chain(cache.find(type=TBag, size=sz1), cache.find(type=TSet, size=sz1)):
                if not isinstance(bag.type.t, THandle):
                    continue

                # if not isinstance(bag, EMapGet):
                #     print("-----> " + pprint(bag) + " : " + pprint(bag.type))
                #     continue
                # print("###> " + pprint(bag) + " : " + pprint(bag.type))
                for binder in self.binders:
                    if binder.type == bag.type.t:
                        for body in cache.find(size=sz2):
                            # experimental filter
                            if binder not in free_vars(body):
                                continue
                            yield EMap(bag, ELambda(binder, body)).with_type(TBag(body.type))
                            if body.type == BOOL:
                                x = EFilter(bag, ELambda(binder, body)).with_type(bag.type)
                                # print("SYNTHESIZED FILT: {}".format(pprint(x)))
                                yield x
                            if isinstance(body.type, TBag):
                                yield EFlatMap(bag, ELambda(binder, body)).with_type(TBag(body.type.t))

        for t in list(cache.types()):
            if isinstance(t, TBag):
                yield EEmptyList().with_type(t)
                for e in cache.find(type=t.t, size=size-1):
                    yield ESingleton(e).with_type(t)

    def with_roots(self, new_roots):
        # return BinderBuilder(self.binders, self.state_vars, list(new_roots) + list(self.roots))
        return BinderBuilder(self.binders, self.state_vars, list(new_roots))

@typechecked
def pick_rep(q_ret : Exp, state : [EVar]) -> ([(EVar, Exp)], Exp):
    cm = CompositeCostModel(state)
    return min(infer_rep(state, q_ret), key=lambda r: cm.split_cost(*r), default=None)

class ImproveQueryJob(jobs.Job):
    def __init__(self, ctx : SynthCtx, state : [EVar], assumptions : [Exp], q : Query, hints : [Exp] = []):
        super().__init__()
        self.ctx = ctx
        self.state = state
        self.assumptions = assumptions
        self.q = q
        self.hints = hints
    def run(self):
        new_ret = self.q.ret
        all_types = self.ctx.all_types

        binders = []
        n_binders = 1 # TODO?
        for t in all_types:
            if isinstance(t, TBag) or isinstance(t, TSet):
                binders += [fresh_var(t.t) for i in range(n_binders)]

        b = BinderBuilder(binders, self.state, [])
        new_rep = [(v, v) for v in self.state]

        try:
            found = False
            for expr in core.improve(
                    target=new_ret,
                    assumptions=EAll(self.assumptions),
                    hints=self.hints,
                    binders=binders,
                    cost_model=CompositeCostModel(self.state),
                    builder=b,
                    stop_callback=lambda: self.stop_requested):

                r = pick_rep(expr, self.state)
                if r is not None:
                    print("SOLUTION")
                    print("-" * 40)
                    for (sv, proj) in r[0]:
                        print("  {} : {} = {}".format(sv.id, pprint(sv.type), pprint(proj)))
                    print("  return {}".format(pprint(r[1])))
                    print("-" * 40)
                    new_rep, new_ret = r
                    found = True
                    break

            if not found:
                import time
                while not self.stop_requested:
                    time.sleep(0.1)
        except core.StopException:
            print("stopping synthesis of {}".format(self.q.name))
            return

        return (new_rep, new_ret)

def rewrite_ret(q : Query, repl) -> Query:
    return Query(
        q.name,
        q.args,
        q.assumptions,
        repl(q.ret))

@typechecked
def synthesize(
        spec      : Spec,
        use_cache : bool = True,
        per_query_timeout : datetime.timedelta = datetime.timedelta(seconds=60)) -> (Spec, dict):

    # gather root types
    types = list(all_types(spec))
    basic_types = set(t for t in types if not isinstance(t, TBag) and not isinstance(t, TSet))
    basic_types |= { BOOL, INT }
    print("basic types:")
    for t in basic_types:
        print("  --> {}".format(pprint(t)))
    basic_types = list(basic_types)
    ctx = SynthCtx(all_types=types, basic_types=basic_types)

    # collect state variables
    state_vars = [EVar(name).with_type(t) for (name, t) in spec.statevars]

    # collect queries
    specs          = [] # query specifications in terms of state_vars
    worklist       = [] # query implementations in terms of new_state_vars
    new_state_vars = [] # list of (var, exp) pairs
    root_queries   = [q.name for q in spec.methods if isinstance(q, Query)]

    # transform ops to delta objects
    ops = [op for op in spec.methods if isinstance(op, Op)]
    op_deltas = { op.name : inc.to_delta(spec.statevars, op) for op in spec.methods if isinstance(op, Op) }

    # op_stms[var][op_name] gives the statement necessary to update
    # `var` when `op_name` is called
    op_stms = nested_dict(2, lambda: SNoOp())

    def push_goal(q : Query):
        specs.append(q)
        rep, ret = pick_rep(q.ret, state_vars)
        set_impl(q, rep, ret)

    def find_spec(q : Query):
        for i in range(len(specs)):
            if specs[i].name == q.name:
                return i
        raise ValueError(q.name)

    def cleanup():
        nonlocal specs
        nonlocal worklist
        nonlocal new_state_vars

        changed = True
        while changed:

            queries_to_keep = set(root_queries)
            class V(BottomUpExplorer):
                def visit_ECall(self, e):
                    queries_to_keep.add(e.func)
            visitor = V()

            for ss in op_stms.values():
                for stm in ss.values():
                    visitor.visit(stm)

            assert all(qname in [qq.name for qq in specs] for qname in queries_to_keep), "WORKLIST={};\nOP_STMS={};\n".format(worklist, op_stms)

            old_specs_len = len(specs)
            old_worklist_len = len(worklist)
            old_state_vars_len = len(new_state_vars)

            specs    = [ q for q in specs    if q.name in queries_to_keep ]
            worklist = [ q for q in worklist if q.name in queries_to_keep ]
            new_state_vars = [ v for v in new_state_vars if any(v[0] in free_vars(q) for q in worklist) ]

            changed = len(specs) != old_specs_len or len(worklist) != old_worklist_len or len(new_state_vars) != old_state_vars_len
            for v in list(op_stms.keys()):
                if v not in [var for (var, exp) in new_state_vars]:
                    del op_stms[v]
                    changed = True

    def set_impl(q : Query, rep : [(EVar, Exp)], ret : Exp):
        i = find_spec(q)
        if i == len(worklist):
            worklist.append(None)
        else:
            assert worklist[i].name == q.name

        to_remove = set()
        for (v, e) in rep:
            aeq = [ vv for (vv, ee) in new_state_vars if alpha_equivalent(e, ee) ]
            if aeq:
                ret = subst(ret, { v.id : aeq[0] })
                to_remove.add(v)
        rep = [ x for x in rep if x[0] not in to_remove ]

        new_state_vars.extend(rep)
        worklist[i] = rewrite_ret(q, lambda prev: ret)

        for op in ops:
            print("###### INCREMENTALIZING: {}".format(op.name))
            (member, delta) = op_deltas[op.name]
            # print(member, delta)
            for new_member, projection in rep:
                (state_update, subqueries) = inc.derivative(projection, member, delta, state_vars)
                # print(state_update, subqueries)
                state_update_stm = inc.apply_delta_in_place(new_member, state_update)
                # print(pprint(state_update_stm))
                for sub_q in subqueries:
                    if any(alpha_equivalent(qq, sub_q) for qq in specs):
                        qq = [qq for qq in specs if alpha_equivalent(qq, sub_q)][0]
                        print("########### subgoal {} is equivalent to {}".format(sub_q.name, qq.name))
                        class Repl(BottomUpRewriter):
                            def visit_ECall(self, e):
                                args = tuple(self.visit(a) for a in e.args)
                                if e.func == sub_q.name:
                                    return ECall(qq.name, args).with_type(e.type)
                                else:
                                    return ECall(e.func, args).with_type(e.type)
                        state_update_stm = Repl().visit(state_update_stm)
                    else:
                        print("########### NEW SUBGOAL: {}".format(pprint(sub_q)))
                        push_goal(sub_q)
                op_stms[new_member][op.name] = state_update_stm

    # set initial implementations
    for q in spec.methods:
        if isinstance(q, Query):
            push_goal(q)

    # start jobs
    timeout = Timeout(per_query_timeout)
    while not timeout.is_timed_out():
        hints = []
        substitutions = { }
        for (v, e) in new_state_vars:
            substitutions[v.id] = e
            hints.append(e)

        print("Starting round! |worklist|={}".format(len(worklist)))

        js = [ImproveQueryJob(ctx, state_vars, list(spec.assumptions) + q.assumptions, rewrite_ret(q, lambda ret: subst(ret, substitutions)), hints) for q in worklist]
        for j in js:
            j.start()
        try:
            job = jobs.wait_any(js, timeout)
            for j in js:
                j.stop()
            if not job.successful:
                raise Exception("job failed")
            updated_query = job.q
            print("found improvement for {}".format(updated_query.name))
            new_rep, new_ret = job.result
            set_impl(updated_query, new_rep, new_ret)
            cleanup()
        except TimeoutException:
            for j in js:
                j.stop()
            break

    new_ops = []
    for op in ops:
        stms = [ ss[op.name] for ss in op_stms.values() ]
        if isinstance(op_deltas[op.name][1], inc.BagElemUpdated):
            stms.append(op.body)
        new_stms = seq(stms)
        new_ops.append(Op(
            op.name,
            op.args,
            [],
            new_stms))

    state_var_exps = { }
    for (v, e) in new_state_vars:
        state_var_exps[v.id] = e
    new_statevars = [(v, e.type) for (v, e) in state_var_exps.items()]
    return (Spec(
        spec.name,
        spec.types,
        spec.extern_funcs,
        new_statevars,
        [],
        worklist + new_ops), state_var_exps)
