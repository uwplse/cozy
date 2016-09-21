#!/usr/bin/env python

"""
Main entry point for synthesis. Run with --help for options.
"""

from __future__ import print_function
import sys
import argparse

import parse
import compile
import common
import typecheck
import syntax
import target_syntax
import syntax_tools
import synth2

def read_file(f):
    with open(f, "r"):
        return f.read()

HINTS = True

def run():
    parser = argparse.ArgumentParser(description='Data structure synthesizer.')

    java_opts = parser.add_argument_group("Java codegen")
    java_opts.add_argument("--java", metavar="FILE.java", default=None, help="Output file for java classes, use '-' for stdout")

    parser.add_argument("file", nargs="?", default=None, help="Input file (omit to use stdin)")
    args = parser.parse_args()

    input_text = sys.stdin.read() if args.file is None else read_file(args.file)
    ast = parse.parse(input_text)

    errors = typecheck.typecheck(ast)
    if errors:
        for e in errors:
            print("Error: {}".format(e))
        sys.exit(1)

    print(ast)
    print()
    print(syntax_tools.pprint(ast))

    # gather root types
    types = syntax_tools.all_types(ast)

    # rewrite enums
    enum_types = [t for t in types if isinstance(t, syntax.TEnum)]
    repl = {
        name : syntax.EEnumEntry(name).with_type(t)
        for t in enum_types
        for name in t.cases }
    ast = syntax_tools.subst(ast, repl)

    # synthesis
    import synth_core
    qs = [q for q in ast.methods if isinstance(q, syntax.Query) if q.name == "inMemEntries"]

    # qs = [q for q in ast.methods if isinstance(q, syntax.Query) if q.name in ("totalMemSize", "totalDiskSize")]
    # qs = [q for q in ast.methods if isinstance(q, syntax.Query)]
    # qs = [qs[0]]
    assert len(qs) > 0
    res_type = syntax.TTuple(tuple(q.ret.type for q in qs)) if len(qs) > 1 else qs[0].ret.type

    def all_exps(e):
        class V(syntax_tools.BottomUpExplorer):
            def join(self, x, children):
                for child in children:
                    yield from child
                if isinstance(x, syntax.Exp):
                    yield x
        return V().visit(e)

    common_roots = list(repl.values())
    print("Common roots:")
    for e in common_roots:
        print("  --> {} : {}".format(syntax_tools.pprint(e), syntax_tools.pprint(e.type)))
    if HINTS:
        state_var_names = set(name for (name, t) in ast.statevars)
        state_roots = set(common_roots)
        print("State hints:")
        for q in qs:
            for e in all_exps(q.ret):
                bound_vars = [fv for fv in syntax_tools.free_vars(e) if fv.id not in state_var_names]
                remap = { v.id : synth_core.EHole(common.fresh_name(), v.type, None) for v in bound_vars }
                e = syntax_tools.subst(e, remap)
                if True or not any(syntax_tools.alpha_equivalent(e, root) for root in state_roots):
                    # if not bound_vars:
                    state_roots.add(e)
                    print("  --> {}".format(syntax_tools.pprint(e)))
        state_roots = list(state_roots)
        # return
    else:
        state_roots = []
        for (name, t) in ast.statevars:
            state_roots.append(syntax.EVar(name).with_type(t))

    basic_types = set(t for t in types if not isinstance(t, syntax.TBag))
    basic_types |= { syntax.TBool(), syntax.TInt() }
    print("basic types:")
    for t in basic_types:
        print("  --> {}".format(syntax_tools.pprint(t)))
    basic_types = list(basic_types)

    class TopLevelBuilder(synth_core.Builder):
        def __init__(self):
            super().__init__((), basic_types)
            self.args_by_q = { q.name: [syntax.EVar(common.fresh_name(name)).with_type(t) for (name, t) in q.args] for q in qs }
            self.state_var_name = common.fresh_name("state")
            # self.state_hole_name = common.fresh_name("state")
        def make_state_hole_core(self, type, builder):
            builder.build_maps = False
            builder.build_tuples = False
            return synth_core.EHole(common.fresh_name(), type, builder)
        def make_state_hole(self, type, builder=None):
            if builder is None:
                builder = synth_core.Builder(state_roots, basic_types)
            if isinstance(type, syntax.TMap):
                # TODO: HACK
                for size in range(1, 3):
                    for t in self.enum_types(size, allow_maps=False):
                        bag_type = syntax.TBag(t)
                        e = syntax.EVar(common.fresh_name()).with_type(t)
                        es = syntax.EVar(common.fresh_name()).with_type(bag_type)
                        khole = synth_core.EHole(common.fresh_name(), type.k, builder.with_roots([e], build_maps=False))
                        vhole = synth_core.EHole(common.fresh_name(), type.v, builder.with_roots([es], build_maps=False))
                        for bag in self.make_state_hole(bag_type, builder):
                            yield target_syntax.EMakeMap(
                                bag,
                                target_syntax.ELambda(e, khole),
                                target_syntax.ELambda(es, vhole)).with_type(type)
            elif isinstance(type, syntax.TTuple):
                if len(type.ts) == 2:
                    for hole1 in self.make_state_hole(type.ts[0], builder):
                        for hole2 in self.make_state_hole(type.ts[1], builder):
                            yield syntax.ETuple((hole1, hole2)).with_type(type)
                else:
                    for hole in self.make_state_hole(type.ts[0], builder):
                        for rest in self.make_state_hole(syntax.TTuple(type.ts[1:]), builder):
                            yield syntax.ETuple((hole,) + rest.es).with_type(type)
            else:
                yield self.make_state_hole_core(type, builder)
        def make_query_hole(self, q, state_var):
            args = self.args_by_q[q.name]
            # for e in common_roots + args + [state_var]:
            #     print("{} : {}".format(syntax_tools.pprint(e), syntax_tools.pprint(e.type)))
            b = synth_core.Builder(common_roots + args + [state_var], basic_types)
            b.build_maps = False
            b.build_tuples = False
            return synth_core.EHole(q.name, q.ret.type, b)
        def build(self, cache, size):
            # TODO: HACK
            for state_type in (syntax.TMap(syntax.TBool(), syntax.TBag([t for t in basic_types if isinstance(t, syntax.THandle)][0])),):
            # for state_type in self.enum_types(size - 1):
                # print(syntax_tools.pprint(state_type))
                state_var = syntax.EVar(self.state_var_name).with_type(state_type)
                for state_hole in self.make_state_hole(state_type):
                    # print("{} --> {}".format(syntax_tools.pprint(state_type), syntax_tools.pprint(state_hole)))

                    out = []
                    for q in qs:
                        q_hole = self.make_query_hole(q, state_var)
                        out.append(q_hole)

                    yield target_syntax.EApp(
                        target_syntax.ELambda(state_var, syntax.ETuple(tuple(out)) if len(out) > 1 else out[0]),
                        state_hole).with_type(res_type)

    builder = TopLevelBuilder()
    if False:
        for q in qs:
            hole = synth_core.EHole(common.fresh_name(), q.ret.type, synth_core.Builder(common_roots + [syntax.EVar(name).with_type(t) for (name, t) in q.args] + state_roots, basic_types))
            spec = syntax.EBinOp(hole, "==", q.ret).with_type(syntax.TBool())
            for mapping in synth_core.synth(spec):
                print("SOLUTION FOR {}".format(q.name))
                type = mapping[hole.name].type
                result = synth_core.expand(hole, mapping)
                print("  {}".format(syntax_tools.pprint(result)))
                # break
        return

    hole = synth_core.EHole(common.fresh_name(), res_type, builder)
    target = tuple(syntax_tools.subst(q.ret, { a1name:a2 for ((a1name, type), a2) in zip(q.args, builder.args_by_q[q.name]) }) for q in qs)
    if len(target) == 1:
        target = target[0]
    else:
        target = syntax.ETuple(target)
    spec = syntax.EBinOp(hole, "==", target)
    print(syntax_tools.pprint(spec))

    for mapping in synth_core.synth(spec):

        print("SOLUTION")
        expr = synth_core.expand(hole, mapping)
        result = expr.arg
        type = result.type
        print("{} : {} = {}".format(
            builder.state_var_name,
            syntax_tools.pprint(type),
            syntax_tools.pprint(result)))

        for q in qs:
            hole = synth_core.EHole(q.name, q.ret.type, None)
            result = synth_core.expand(hole, mapping)
            print("{} =".format(q.name))
            print("  {}".format(syntax_tools.pprint(result)))

        return

    # if args.java is not None:
    #     with common.open_maybe_stdout(args.java) as out:
    #         out.write(compile.JavaPrinter().visit(ast))

if __name__ == "__main__":
    run()
