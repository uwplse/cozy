#!/usr/bin/env python

"""
Main entry point for synthesis. Run with --help for options.
"""

from __future__ import print_function
import sys
import argparse

import parse
import compile
import typecheck
import syntax_tools
import synthesis

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

    ast = synthesis.synthesize(ast)
    print()
    print(syntax_tools.pprint(ast))

    # if args.java is not None:
    #     with common.open_maybe_stdout(args.java) as out:
    #         out.write(compile.JavaPrinter().visit(ast))

if __name__ == "__main__":
    run()
