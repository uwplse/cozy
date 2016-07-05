#!/usr/bin/env python

"""
Main entry point for synthesis. Run with --help for options.
"""

from __future__ import print_function
import sys
import pprint

import parse
import compile
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

    ast = synth2.synthesize(ast)
    print(syntax_tools.pprint(ast))
    # print(compile.JavaPrinter().visit(ast))

if __name__ == "__main__":
    run()
