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

    # rewrite enums
    enum_types = [t for (name, t) in ast.types if isinstance(t, syntax.TEnum)]
    repl = { name : syntax.EEnumEntry(name).with_type(t) for t in enum_types for name in t.cases }
    ast = syntax_tools.subst(ast, repl)

    # synthesis
    import synth_core
    qs = [q for q in ast.methods if isinstance(q, syntax.Query) if q.name == "pendingEntries"]

    common_roots = list(repl.values())
    state_roots = []
    for (name, t) in ast.statevars:
        state_roots.append(syntax.EVar(name).with_type(t))

    INT  = syntax.TInt()
    LONG = syntax.TLong()
    BOOL = syntax.TBool()
    ht = syntax.THandle("entries")
    ht.value_type = { name:t for (name, t) in ast.types }["Entry"]
    state_type = syntax.TBag(ht) # TODO
    state_var = syntax.EVar(common.fresh_name("state")).with_type(state_type)
    state_hole = synth_core.EHole("state", state_var.type, synth_core.Builder(common_roots + state_roots))

    spec = syntax.EBool(True).with_type(BOOL)
    for q in qs:
        args = [syntax.EVar(name).with_type(t) for (name, t) in q.args]
        q_hole = synth_core.EHole(q.name, q.ret.type, synth_core.Builder(common_roots + args + [state_var]))
        q_spec = syntax.EBinOp(q_hole, "==", q.ret).with_type(BOOL)
        spec = syntax.EBinOp(spec, "and", q_spec)

    spec = target_syntax.EApp(target_syntax.ELambda(state_var, spec), state_hole)
    # spec = syntax_tools.implies(
    #     syntax.EUnaryOp(),
    #     spec)

    print(syntax_tools.pprint(spec))
    print(repr(spec))

    for mapping in synth_core.synth(spec):
        result = synth_core.expand(q_hole, mapping)
        print(syntax_tools.pprint(result))
        return

    # ast = synth2.synthesize(ast)
    # print(syntax_tools.pprint(ast))

    # if args.java is not None:
    #     with common.open_maybe_stdout(args.java) as out:
    #         out.write(compile.JavaPrinter().visit(ast))

if __name__ == "__main__":
    run()
