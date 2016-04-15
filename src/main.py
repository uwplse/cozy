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
import syntax_tools

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
    print(compile.JavaPrinter().visit(ast))
    print(syntax_tools.pprint(ast))

if __name__ == "__main__":
    run()
