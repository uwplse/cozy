#!/usr/bin/env python

"""
Main entry point for synthesis. Run with --help for options.
"""

import sys
import traceback
import argparse
import os.path

from synthesis import SolverContext
from parse import parseQuery
import cost_model
from codegen_java import write_java
from codegen_cpp import write_cpp

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Data structure synthesizer.')

    parser.add_argument("--java", metavar="FILE.java", default=None, help="Output file for java classes, use '-' for stdout")
    parser.add_argument("--java-package", metavar="com.java.pkg", default=None, help="Java package for generated structure")

    parser.add_argument("--cpp", metavar="FILE.cpp", default=None, help="Output file for C++ code, use '-' for stdout")
    parser.add_argument("--cpp-header", metavar="FILE.hpp", default=None, help="Output file for C++ header, use '-' for stdout")
    parser.add_argument("--cpp-namespace", metavar="ns", default=None, help="C++ namespace")

    parser.add_argument("file", nargs="?", default=None, help="Input file (omit to use stdin)")
    args = parser.parse_args()

    if args.file is not None:
        with open(args.file, "r") as f:
            inp = f.read()
    else:
        inp = sys.stdin.read()

    fields, qvars, assumptions, q, cost_model_file = parseQuery(inp)

    if cost_model_file is not None and args.file is None:
        raise Exception("cannot locate {}".format(cost_model_file))

    if cost_model_file is not None:
        # cost_model_file should be specified relative to the input file
        cost_model_file = os.path.abspath(os.path.join(
            os.path.dirname(args.file),
            cost_model_file))

    sc = SolverContext(
        varNames=[v for v,ty in qvars],
        fieldNames=[f for f,ty in fields],
        cost_model=lambda plan: cost_model.cost(fields, qvars, plan, cost_model_file),
        assumptions=assumptions)
    for a in assumptions:
        print "Assuming:", a
    print "Query:", q

    bestCost = None
    bestPlan = None

    seen = set()

    try:
        for p in sc.synthesizePlansByEnumeration(q):
            if p in seen:
                continue
            seen.add(p)
            cost = p.cost
            improvement = False
            if bestCost is None or cost < bestCost:
                improvement = True
                bestPlan = p
                bestCost = cost
            print "FOUND PLAN: ", p, "; cost = ", cost, (" *** IMPROVEMENT" if improvement else "")
    except:
        print "stopping due to exception"
        traceback.print_exc()

    if bestPlan is not None:
        print "="*60
        print "Best plan found: ", bestPlan
        print "Best plan size: ", bestPlan.size()
        print "Cost: ", bestCost

        java_writer = lambda x: None
        if args.java is not None:
            java_writer = sys.stdout.write if args.java == "-" else open(args.java, "w").write

        write_java(fields, qvars, bestPlan, java_writer, package=args.java_package)

        cpp_writer = lambda x: None
        if args.cpp is not None:
            cpp_writer = sys.stdout.write if args.cpp == "-" else open(args.cpp, "w").write

        cpp_header_writer = lambda x: None
        if args.cpp_header is not None:
            cpp_header_writer = sys.stdout.write if args.cpp_header == "-" else open(args.cpp_header, "w").write

        write_cpp(fields, qvars, bestPlan, cpp_writer, cpp_header_writer, namespace=args.cpp_namespace)
