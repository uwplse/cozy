#!/usr/bin/env python

"""
Main entry point for synthesis. Run with --help for options.
"""

from __future__ import print_function
import sys

import parse

def run():
    stdin = sys.stdin.read()
    print(stdin)

    for tok in parse.tokenize(stdin):
        print(tok, end=" ")
    print()

    print(parse.parse(stdin))

if __name__ == "__main__":
    run()
