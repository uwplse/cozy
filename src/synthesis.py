from collections import namedtuple

from common import typechecked, fresh_name
from target_syntax import *
from syntax_tools import all_types, alpha_equivalent, BottomUpExplorer, free_vars, pprint, subst, implies
import synth_core
from typecheck import INT, BOOL

HINTS = True

SynthCtx = namedtuple("SynthCtx", ["all_types", "basic_types"])

def all_exps(e):
    class V(BottomUpExplorer):
        def join(self, x, children):
            for child in children:
                yield from child
            if isinstance(x, Exp):
                yield x
    return V().visit(e)

def fragmentize(exp : Exp, bound_names : {str} = set()):
    so_far = []
    for e in all_exps(exp):
        fvs = [fv for fv in free_vars(e) if fv.id not in bound_names]
        remap = { v.id : synth_core.EHole(fresh_name(), v.type, None) for v in fvs }
        e = subst(e, remap)
        if not any(alpha_equivalent(e, root) for root in so_far):
            so_far.append(e)
            yield e

@typechecked
def synthesize_queries(ctx : SynthCtx, state : [EVar], assumptions : [Exp], queries : [Query]): # -> (EVar, Exp, [Query]):
    """
    Synthesize efficient re-implementations for the given queries.

    Input:
        ctx     - a synthesis context for the problem
        state   - list of state variables
        queries - a list of queries in the specification

    Output:
        (new_state, state_proj, new_queries)
    where
        new_state is a variable
        state_proj is an expression mapping state to new_state
        new_queries is a list of new query expressions
    """
    assert len(queries) > 0

    res_type = TTuple(tuple(q.ret.type for q in queries)) if len(queries) > 1 else queries[0].ret.type
    all_types = ctx.all_types
    basic_types = ctx.basic_types

    if HINTS:
        state_var_names = set(v.id for v in state)
        state_roots = list(fragmentize(ETuple(tuple(q.ret for q in queries)).with_type(res_type) if len(queries) > 1 else queries[0].ret, bound_names=state_var_names))
    else:
        state_roots = list(state)
        for t in basic_types:
            if isinstance(t, TEnum):
                for case in t.cases:
                    state_roots.append(EEnumEntry(case).with_type(t))
    print("State roots:")
    for r in state_roots:
        print("  --> {}".format(pprint(r)))

    class TopLevelBuilder(synth_core.Builder):
        def __init__(self):
            super().__init__((), basic_types)
            self.args_by_q = { q.name: [EVar(fresh_name(name)).with_type(t) for (name, t) in q.args] for q in queries }
            self.state_var_name = fresh_name("state")
            # self.state_hole_name = fresh_name("state")
        def make_state_hole_core(self, type, builder):
            builder.build_maps = False
            builder.build_tuples = False
            return synth_core.EHole(fresh_name(), type, builder)
        def make_state_hole(self, type, builder=None):
            if builder is None:
                builder = synth_core.Builder(state_roots, basic_types)
            if isinstance(type, TMap):
                for t in all_types:
                    if isinstance(t, TBag):
                        bag_type = t
                        for r in state_roots:
                            holes = list(synth_core.find_holes(r))
                            if r.type == type.k and len(holes) == 1 and holes[0].type == bag_type.t:
                                e = EVar(fresh_name()).with_type(bag_type.t)
                                es = EVar(fresh_name()).with_type(bag_type)
                                vhole = synth_core.EHole(fresh_name(), type.v, builder.with_roots([es], build_maps=False))
                                for bag in self.make_state_hole(bag_type, builder):
                                    yield EMakeMap(
                                        bag,
                                        ELambda(e, subst(r, { holes[0].name : e })),
                                        ELambda(es, vhole)).with_type(type)
            elif isinstance(type, TTuple):
                if len(type.ts) == 2:
                    for hole1 in self.make_state_hole(type.ts[0], builder):
                        for hole2 in self.make_state_hole(type.ts[1], builder):
                            yield ETuple((hole1, hole2)).with_type(type)
                else:
                    for hole in self.make_state_hole(type.ts[0], builder):
                        for rest in self.make_state_hole(TTuple(type.ts[1:]), builder):
                            yield ETuple((hole,) + rest.es).with_type(type)
            else:
                yield self.make_state_hole_core(type, builder)
        def make_query_hole(self, q, state_var):
            args = self.args_by_q[q.name]
            b = synth_core.Builder(args + [state_var], basic_types)
            b.build_maps = False
            b.build_tuples = False
            return synth_core.EHole(q.name, q.ret.type, b)
        def build(self, cache, size):
            # TODO: HACK
            # cheat = TMap(TBool(), TBag([t for t in basic_types if isinstance(t, THandle)][0]))
            # cheat = TTuple((TInt(), TInt()))
            # if size != 1: return
            # for state_type in (cheat,):
            for state_type in self.enum_types(size - 1, allow_tuples=False):
                # if state_type == cheat:
                #     print("now exploring {}".format(pprint(state_type)))
                # print("state ?= {}".format(pprint(state_type)))
                # print(pprint(state_type))
                state_var = EVar(self.state_var_name).with_type(state_type)
                for state_hole in self.make_state_hole(state_type):
                    # print("   --> {}".format(pprint(state_hole)))
                    # print("{} --> {}".format(pprint(state_type), pprint(state_hole)))

                    out = []
                    for q in queries:
                        q_hole = self.make_query_hole(q, state_var)
                        out.append(q_hole)

                    yield EApp(
                        ELambda(state_var, ETuple(tuple(out)) if len(out) > 1 else out[0]),
                        state_hole).with_type(res_type)

    builder = TopLevelBuilder()
    hole = synth_core.EHole(fresh_name(), res_type, builder)
    target = tuple(subst(q.ret, { a1name:a2 for ((a1name, type), a2) in zip(q.args, builder.args_by_q[q.name]) }) for q in queries)
    if len(target) == 1:
        target = target[0]
    else:
        target = ETuple(target)

    assumption = EBool(True).with_type(BOOL)
    for a in assumptions:
        assumption = EBinOp(assumption, "and", a).with_type(BOOL)
    spec = implies(assumption, EBinOp(hole, "==", target))
    print(pprint(spec))

    for mapping in synth_core.synth(spec):

        print("SOLUTION")
        expr = synth_core.expand(hole, mapping)
        result = expr.arg
        type = result.type
        print("{} : {} = {}".format(
            builder.state_var_name,
            pprint(type),
            pprint(result)))

        for q in queries:
            hole = synth_core.EHole(q.name, q.ret.type, None)
            result = synth_core.expand(hole, mapping)
            print("{} =".format(q.name))
            print("  {}".format(pprint(result)))

        return

@typechecked
def synthesize(spec : Spec):
    """
    Main synthesis routine.
    """

    # gather root types
    types = all_types(spec)
    basic_types = set(t for t in types if not isinstance(t, TBag))
    basic_types |= { TBool(), TInt() }
    print("basic types:")
    for t in basic_types:
        print("  --> {}".format(pprint(t)))
    basic_types = list(basic_types)
    ctx = SynthCtx(all_types=types, basic_types=basic_types)

    # rewrite enums
    enum_types = [t for t in basic_types if isinstance(t, TEnum)]
    repl = {
        name : EEnumEntry(name).with_type(t)
        for t in enum_types
        for name in t.cases }
    spec = subst(spec, repl)

    # collect queries
    # qs = [qs[0]]
    # qs = [q for q in spec.methods if isinstance(q, Query) if q.name == "inMemEntries"]
    # qs = [q for q in spec.methods if isinstance(q, Query) if q.name in ("totalMemSize", "totalDiskSize")]
    qs = [q for q in spec.methods if isinstance(q, Query)]
    # assert len(qs) > 0

    # synthesis
    for q in qs:
        print("##### SYNTHESIZING {}".format(q.name))
        synthesize_queries(ctx, [EVar(name).with_type(t) for (name, t) in spec.statevars], list(spec.assumptions), [q])

    raise NotImplementedError()
