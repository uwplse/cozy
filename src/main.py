#!/usr/bin/env python

"""
Main entry point for synthesis. Run with --help for options.
"""

import collections
import sys
import argparse
import os.path
import itertools
import pickle

from synthesis import SolverContext
from parse import parseQuery
import cost_model
from codegen import enumerate_impls
from codegen_java import JavaCodeGenerator
from codegen_cpp import CppCodeGenerator

def pickBestImpls(fields, queries, cost_model_file):
    bestImpls = None
    bestScore = None
    for impls in enumerate_impls(fields, queries):
        if cost_model_file is None:
            return impls
        score = cost_model.dynamic_cost(fields, queries, impls, cost_model_file)
        if bestImpls is None or score > bestScore:
            bestImpls = impls
            bestScore = score
    return bestImpls

def highlevel_synthesis(all_input, fields, assumptions, query, enable_cache, timeout):
    """sets .bestPlans on the query object"""

    key = hash((all_input, query.name))
    cache_file = "/tmp/{}.pickle".format(key)
    if enable_cache:
        try:
            with open(cache_file, "rb") as f:
                bestPlans = pickle.load(f)
            print "loaded cache file {} for query {}".format(cache_file, query.name)
            query.bestPlans = bestPlans
            return
        except Exception as e:
            print "failed to load cache file {}: {}".format(cache_file, e)

    local_assumptions = list(itertools.chain(assumptions, query.assumptions))
    sc = SolverContext(
        varNames=[v for v,ty in query.vars],
        fieldNames=[f for f,ty in fields],
        cost_model=lambda plan: cost_model.cost(fields, query.vars, plan),
        assumptions=local_assumptions)
    print "Query {}: {}".format(query.name, query.pred)
    for a in local_assumptions:
        print "  --> assuming:", a

    query.bestPlans = set(sc.synthesizePlansByEnumeration(query.pred, sort_field=query.sort_field, timeout=timeout))

    try:
        with open(cache_file, "wb") as f:
            pickle.dump(query.bestPlans, f)
    except Exception as e:
        print "failed to save cache file {}: {}".format(cache_file, e)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Data structure synthesizer.')

    parser.add_argument("-d", "--disable-cache", action="store_true", help="Disable caching synthesis results")
    parser.add_argument("-t", "--timeout", metavar="N", default=None, help="Per-query synthesis timeout (in seconds)")

    parser.add_argument("--java", metavar="FILE.java", default=None, help="Output file for java classes, use '-' for stdout")
    parser.add_argument("--java-package", metavar="com.java.pkg", default=None, help="Java package for generated structure")
    parser.add_argument("--java-class", metavar="Name", default="DataStructure", help="Java class name for generated structure")

    parser.add_argument("--cpp", metavar="FILE.cpp", default=None, help="Output file for C++ code, use '-' for stdout")
    parser.add_argument("--cpp-header", metavar="FILE.hpp", default=None, help="Output file for C++ header, use '-' for stdout")
    parser.add_argument("--cpp-class", metavar="Name", default="DataStructure", help="C++ class name for generated structure")
    parser.add_argument("--cpp-extra", metavar="cpp-code", default=None, help="Extra text to include at top of C++ header file")
    parser.add_argument("--cpp-namespace", metavar="ns", default=None, help="C++ namespace")

    parser.add_argument("file", nargs="?", default=None, help="Input file (omit to use stdin)")
    args = parser.parse_args()

    if args.file is not None:
        with open(args.file, "r") as f:
            inp = f.read()
    else:
        inp = sys.stdin.read()

    fields, assumptions, queries, cost_model_file = parseQuery(inp)

    if cost_model_file is not None and args.file is None:
        raise Exception("cannot locate {}".format(cost_model_file))

    if cost_model_file is not None:
        # cost_model_file should be specified relative to the input file
        cost_model_file = os.path.abspath(os.path.join(
            os.path.dirname(args.file),
            cost_model_file))

    for query in queries:
        highlevel_synthesis(inp, fields, assumptions, query, enable_cache=(not args.disable_cache), timeout=float(args.timeout) if args.timeout else None)
        print "found {} great plans:".format(len(query.bestPlans))
        for plan in query.bestPlans:
            print "    {}".format(plan)

    fields = collections.OrderedDict(fields)
    impls = pickBestImpls(fields, queries, cost_model_file)
    for q, i in zip(queries, impls):
        q.impl = i

    if args.cpp_header is not None or args.cpp is not None:
        cpp_header_writer = (sys.stdout.write if args.cpp_header == "-" else open(args.cpp_header, "w").write) if args.cpp_header else (lambda x: None)
        cpp_writer = (sys.stdout.write if args.cpp == "-" else open(args.cpp, "w").write) if args.cpp else (lambda x: None)
        CppCodeGenerator(
            header_writer=cpp_header_writer,
            code_writer=cpp_writer,
            class_name=args.cpp_class,
            namespace=args.cpp_namespace,
            header_extra=args.cpp_extra).write(fields, queries)

    if args.java is not None:
        java_writer = sys.stdout.write if args.java == "-" else open(args.java, "w").write
        JavaCodeGenerator(java_writer, package_name=args.java_package, class_name=args.java_class).write(fields, queries)
