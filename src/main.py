#!/usr/bin/env python

"""
Main entry point for synthesis. Run with --help for options.
"""

from __future__ import print_function
import sys
import pprint

import parse
import compile
import incrementalization as inc
import typecheck
import syntax
import syntax_tools
import synth2

def run():
    stdin = sys.stdin.read()
    ast = parse.parse(stdin)

    errors = typecheck.typecheck(ast)
    if errors:
        for e in errors:
            print("Error: {}".format(e))
        sys.exit(1)

    pprint.PrettyPrinter(indent=4).pprint(ast)
    print()
    print(syntax_tools.pprint(ast))

    # Synthesis testing
    ds = [inc.to_delta(m) for m in ast.methods if isinstance(m, syntax.Op)]
    ctx = synth2.Context(state=ast.statevars, deltas=ds)
    # fn = [m for m in ast.methods if m.name == "unit"][0]
    goals = [
        synth2.Goal(name=m.name, args=m.args, e=m.ret)
        for m in ast.methods if isinstance(m, syntax.Query)]

    print(synth2.synthesize(ctx, goals))

    # print(compile.JavaPrinter().visit(ast))

if __name__ == "__main__":
    run()
