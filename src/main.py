#!/usr/bin/env python

"""
Main entry point for synthesis. Run with --help for options.
"""

from __future__ import print_function
import sys

import parse

def run():
    stdin = sys.stdin.read()
    ast = parse.parse(stdin)
    print(ast)

if __name__ == "__main__":
    run()
