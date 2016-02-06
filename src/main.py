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
import time

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
        yield CppCodeGenerator(with_qt=args.with_qt)

def pick_best_impls(fields, queries, cost_model_file, code_generators, args):
    bestImpls = None
    bestCost  = None
    bestCG    = None
    for cg in code_generators:
        for impls in enumerate_impls(fields, queries, cg.extensions):
            if cost_model_file is None:
                return impls, cg, 0

            print("benchmarking {} using {}... ".format({q.name : impl for q, impl in zip(queries, impls)}, cg), end="")
            sys.stdout.flush()
            cost = cg.dynamic_cost(fields, queries, impls, cost_model_file, args)
            print("cost = {}".format(cost))

            if bestImpls is None or cost < bestCost:
                bestImpls = impls
                bestCost  = cost
                bestCG    = cg

    return bestImpls, bestCG, bestCost

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

def now():
    return time.time()

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Data structure synthesizer.')

    parser.add_argument("-d", "--disable-cache", action="store_true", help="Disable caching synthesis results")
    parser.add_argument("-t", "--timeout", metavar="N", default=None, help="Per-query synthesis timeout (in seconds)")
    parser.add_argument("--write-timings", metavar="FILE", default=None, help="Write timing information to a side file")

    java_opts = parser.add_argument_group("Java codegen")
    java_opts.add_argument("--java", metavar="FILE.java", default=None, help="Output file for java classes, use '-' for stdout")
    java_opts.add_argument("--java-package", metavar="com.java.pkg", default=None, help="Java package for generated structure")
    java_opts.add_argument("--java-class", metavar="Name", default="DataStructure", help="Java class name for generated structure")
    java_opts.add_argument("--java-extra-classpath", metavar="PATH", default="", help="Path to search for auxiliary Java classes")

    cpp_opts = parser.add_argument_group("C++ codegen")
    cpp_opts.add_argument("--cpp", metavar="FILE.cpp", default=None, help="Output file for C++ code, use '-' for stdout")
    cpp_opts.add_argument("--cpp-header", metavar="FILE.hpp", default=None, help="Output file for C++ header, use '-' for stdout")
    cpp_opts.add_argument("--cpp-class", metavar="Name", default="DataStructure", help="C++ class name for generated structure")
    cpp_opts.add_argument("--cpp-record-class", metavar="Name", default="Record", help="C++ class name for record type")
    cpp_opts.add_argument("--cpp-abstract-record", action="store_true", help="Generate abstract record type (to be filled in by client)")
    cpp_opts.add_argument("--cpp-extra", metavar="cpp-code", default=None, help="Extra text to include at top of C++ header file")
    cpp_opts.add_argument("--cpp-namespace", metavar="ns", default=None, help="C++ namespace")
    cpp_opts.add_argument("--with-qt", action="store_true", help="Allow use of Qt collections classes")

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

    synthesis_times = collections.OrderedDict()
    for query in queries:
        start = now()
        highlevel_synthesis(inp, fields, assumptions, query, enable_cache=(not args.disable_cache), timeout=float(args.timeout) if args.timeout else None)
        synthesis_times[query.name] = now() - start

    for query in queries:
        print("found {} great plans for query '{}':".format(len(query.bestPlans), query.name))
        for plan in query.bestPlans:
            print("    {}".format(plan))

    start = now()
    fields = collections.OrderedDict(fields)
    code_generators = list(cg for cg in enumerate_code_generators(args) if (not cost_model_file) or cg.supports_cost_model_file(cost_model_file))
    impls, cg, cost = pick_best_impls(fields, queries, cost_model_file, code_generators, args)
    autotune_time = now() - start

    if args.write_timings:
        with open(args.write_timings, "w") as f:
            for k, v in synthesis_times.items():
                f.write("synth-{}-time {}\n".format(k, v))
            f.write("synth-time {}\n".format(sum(synthesis_times.values())))
            f.write("autotune-time {}\n".format(autotune_time))

    if impls:
        for q, i in zip(queries, impls):
            q.impl = i
        cg.write(fields, queries, **vars(args))
