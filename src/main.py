#!/usr/bin/env python

"""
Main entry point for synthesis. Run with --help for options.
"""

import sys
import traceback
import argparse

from synthesis import SolverContext
from parse import parseQuery
import cost_model
from codegen_java import write_java

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Data structure synthesizer.')
    parser.add_argument("--java", metavar="FILE.java", default="-", help="Output file for java classes, use '-' for stdout")
    parser.add_argument("--java-package", metavar="com.java.pkg", default=None, help="Java package for generated structure")
    parser.add_argument("file", nargs="?", default=None, help="Input file (omit to use stdin)")
    args = parser.parse_args()

    if args.file is not None:
        with open(args.file, "r") as f:
            inp = f.read()
    else:
        inp = sys.stdin.read()

    fields, qvars, assumptions, q = parseQuery(inp)

    sc = SolverContext(
        varNames=[v for v,ty in qvars],
        fieldNames=[f for f,ty in fields],
        assumptions=assumptions)
    for a in assumptions:
        print "Assuming:", a
    print "Query:", q

    bestCost = None
    bestPlan = None

    try:
        for p in sc.synthesizePlansByEnumeration(q):
            cost = cost_model.cost(p)
            print "FOUND PLAN: ", p, "; cost = ", cost
            if bestCost is None or cost < bestCost:
                bestPlan = p
                bestCost = cost
    except:
        print "stopping due to exception"
        traceback.print_exc()

    print "="*60
    print "Best plan found: ", bestPlan
    print "Best plan size: ", bestPlan.size()
    print "Cost: ", bestCost

    if args.java == "-":
        write_java(fields, qvars, bestPlan, sys.stdout.write)
    else:
        with open(args.java, "w") as f:
            write_java(fields, qvars, bestPlan, f.write, package=args.java_package)
