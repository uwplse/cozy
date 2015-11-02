#!/usr/bin/env python

"""
Main entry point for synthesis. Run with --help for options.
"""

from __future__ import print_function
import collections
import functools
import sys
import argparse
import os.path
import itertools
import pickle
import sys

from synthesis import SolverContext
from parse import parseQuery
import cost_model
from codegen import enumerate_impls
from codegen_java import JavaCodeGenerator
from codegen_cpp import CppCodeGenerator

def enumerate_code_generators(args):
    if args.java is not None:
        yield JavaCodeGenerator()
    elif args.cpp_header is not None or args.cpp is not None:
        yield CppCodeGenerator(maptype="hash")
        yield CppCodeGenerator(maptype="tree")
        yield CppCodeGenerator(maptype="qhash")

def pick_best_impls(fields, queries, cost_model_file, code_generators):
    bestImpls = None
    bestScore = None
    bestCG    = None
    for cg in code_generators:
        for impls in enumerate_impls(fields, queries):
            if cost_model_file is None:
                return impls, cg, 0

            print("benchmarking {}... ".format([q.name for q in queries]), end="")
            sys.stdout.flush()
            try:
                score = cg.dynamic_cost(fields, queries, impls, cost_model_file)
            except Exception as e:
                print("FAILED ({})".format(e))
                continue
            print("cost = {}".format(score))

            if bestImpls is None or score > bestScore:
                bestImpls = impls
                bestScore = score
                bestCG    = cg

    return bestImpls, bestCG, bestScore

def highlevel_synthesis(all_input, fields, assumptions, query, enable_cache, timeout):
    """sets .bestPlans on the query object"""

    key = hash((all_input, query.name))
    cache_file = "/tmp/{}.pickle".format(key)
    if enable_cache:
        try:
            with open(cache_file, "rb") as f:
                bestPlans = pickle.load(f)
            print("loaded cache file {} for query {}".format(cache_file, query.name))
            query.bestPlans = bestPlans
            return
        except Exception as e:
            print("failed to load cache file {}: {}".format(cache_file, e))

    local_assumptions = list(itertools.chain(assumptions, query.assumptions))
    sc = SolverContext(
        varNames=[v for v,ty in query.vars],
        fieldNames=[f for f,ty in fields],
        cost_model=lambda plan: cost_model.cost(fields, query.vars, plan),
        assumptions=local_assumptions)
    print("Query {}: {}".format(query.name, query.pred))
    for a in local_assumptions:
        print("  --> assuming:", a)

    query.bestPlans = set(sc.synthesizePlansByEnumeration(query.pred, sort_field=query.sort_field, timeout=timeout))

    try:
        with open(cache_file, "wb") as f:
            pickle.dump(query.bestPlans, f)
    except Exception as e:
        print("failed to save cache file {}: {}".format(cache_file, e))

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Data structure synthesizer.')

    parser.add_argument("-d", "--disable-cache", action="store_true", help="Disable caching synthesis results")
    parser.add_argument("-t", "--timeout", metavar="N", default=None, help="Per-query synthesis timeout (in seconds)")

    java_opts = parser.add_argument_group("Java codegen")
    java_opts.add_argument("--java", metavar="FILE.java", default=None, help="Output file for java classes, use '-' for stdout")
    java_opts.add_argument("--java-package", metavar="com.java.pkg", default=None, help="Java package for generated structure")
    java_opts.add_argument("--java-class", metavar="Name", default="DataStructure", help="Java class name for generated structure")

    cpp_opts = parser.add_argument_group("C++ codegen")
    cpp_opts.add_argument("--cpp", metavar="FILE.cpp", default=None, help="Output file for C++ code, use '-' for stdout")
    cpp_opts.add_argument("--cpp-header", metavar="FILE.hpp", default=None, help="Output file for C++ header, use '-' for stdout")
    cpp_opts.add_argument("--cpp-class", metavar="Name", default="DataStructure", help="C++ class name for generated structure")
    cpp_opts.add_argument("--cpp-record-class", metavar="Name", default="Record", help="C++ class name for record type")
    cpp_opts.add_argument("--cpp-extra", metavar="cpp-code", default=None, help="Extra text to include at top of C++ header file")
    cpp_opts.add_argument("--cpp-namespace", metavar="ns", default=None, help="C++ namespace")

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

    for query in queries:
        print("found {} great plans for query '{}':".format(len(query.bestPlans), query.name))
        for plan in query.bestPlans:
            print("    {}".format(plan))

    fields = collections.OrderedDict(fields)
    code_generators = list(cg for cg in enumerate_code_generators(args) if (not cost_model_file) or cg.supports_cost_model_file(cost_model_file))
    impls, cg, score = pick_best_impls(fields, queries, cost_model_file, code_generators)

    if impls:
        for q, i in zip(queries, impls):
            q.impl = i
        cg.write(fields, queries, **vars(args))

        # if args.cpp_header is not None or args.cpp is not None:
        #     cpp_header_writer = (sys.stdout.write if args.cpp_header == "-" else open(args.cpp_header, "w").write) if args.cpp_header else (lambda x: None)
        #     cpp_writer = (sys.stdout.write if args.cpp == "-" else open(args.cpp, "w").write) if args.cpp else (lambda x: None)
        #     CppCodeGenerator(
        #         header_writer=cpp_header_writer,
        #         code_writer=cpp_writer,
        #         class_name=args.cpp_class,
        #         namespace=args.cpp_namespace,
        #         header_extra=args.cpp_extra).write(fields, queries)

        # if args.java is not None:
        #     java_writer = sys.stdout.write if args.java == "-" else open(args.java, "w").write
        #     JavaCodeGenerator(java_writer, package_name=args.java_package, class_name=args.java_class).write(fields, queries)
