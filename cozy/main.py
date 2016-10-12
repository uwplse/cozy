#!/usr/bin/env python

"""
Main entry point for synthesis. Run with --help for options.
"""

from __future__ import print_function
import sys
import argparse

from cozy import parse
from cozy import compile
from cozy import common
from cozy import typecheck
from cozy import desugar
from cozy import target_syntax
from cozy import syntax_tools
from cozy import synthesis
from cozy import library
from cozy import autotuning
from cozy import solver

def read_file(filename):
    with open(filename, "r") as f:
        return f.read()

@common.typechecked
def compute_sharing(state_map : dict, true_types : dict) -> dict:
    """
    Takes a dictionary mapping { state_var_id : state_exp } and a
    dictionary mapping { state_var_id : refined_type } and returns
    a dictionary { ht : groups } for each handle type ht. Each group
    is a list of implementation types whose intrusive data will
    never be used at the same time.
    """

    def uses_intrusive_data(e, handle):
        if isinstance(e, target_syntax.EMakeMap):
            if isinstance(e.e.type, target_syntax.TBag) and e.e.type.t == handle.type:
                k = e.key.apply_to(handle)
                kk = syntax_tools.fresh_var(k.type, "k")
                return uses_intrusive_data(e.value.apply_to(target_syntax.EFilter(e.e, target_syntax.ELambda(handle, syntax_tools.equal(k, kk)))), handle)
            return target_syntax.EBool(False).with_type(target_syntax.TBool())
        elif isinstance(e, target_syntax.EFilter):
            return target_syntax.EAll([uses_intrusive_data(e.e, handle), e.p.apply_to(handle)])
        elif isinstance(e, target_syntax.EMap):
            return uses_intrusive_data(e.e, handle)
        elif isinstance(e, target_syntax.EUnaryOp):
            return uses_intrusive_data(e.e, handle)
        elif isinstance(e, target_syntax.EVar):
            if isinstance(e.type, target_syntax.TBag) and e.type.t == handle.type:
                return target_syntax.EBinOp(handle, "in", e).with_type(target_syntax.TBool())
            return target_syntax.EBool(False).with_type(target_syntax.TBool())
        else:
            raise NotImplementedError(e)

    types = set(t for e in state_map.values() for t in syntax_tools.all_types(e.type))
    handle_types = set(t for t in types if isinstance(t, target_syntax.THandle))
    out = { }

    # for (var, exp) in state_map.items():
    #     print(" --> {} = {}".format(var, syntax_tools.pprint(exp)))

    for ht in handle_types:
        groups = []
        handle = syntax_tools.fresh_var(ht, "handle")
        # print(ht)
        # for (var, exp) in state_map.items():
        #     print(" --> {} iff {}".format(var, syntax_tools.pprint(uses_intrusive_data(exp, handle))))

        type_uses_intrusive_data = { }
        for (var, exp) in state_map.items():
            use = uses_intrusive_data(exp, handle)
            for t in syntax_tools.all_types(true_types[var]):
                # print(syntax_tools.pprint(t))
                if hasattr(t, "intrusive_data"):
                    type_uses_intrusive_data[t] = use
                # else:
                #     print("     no intrusive data for " + syntax_tools.pprint(t))

        # print(type_uses_intrusive_data)

        for t, cond in type_uses_intrusive_data.items():
            found = False
            for g in groups:
                if all(not solver.satisfy(target_syntax.EAll([cond, type_uses_intrusive_data[t]])) for t in g):
                    found = True
                    g.append(t)
                    break
            if not found:
                groups.append([t])

        # print("    --> {}".format(groups))
        out[ht] = groups

    return out

def run():
    parser = argparse.ArgumentParser(description='Data structure synthesizer.')
    parser.add_argument("-d", "--disable-cache", action="store_true", help="Disable caching of synthesis results")

    java_opts = parser.add_argument_group("Java codegen")
    java_opts.add_argument("--java", metavar="FILE.java", default=None, help="Output file for java classes, use '-' for stdout")
    java_opts.add_argument("--package", metavar="pkg.name", default=None, help="Java package name")

    cxx_opts = parser.add_argument_group("C++ codegen")
    cxx_opts.add_argument("--c++", metavar="FILE.h", default=None, help="Output file for C++ (header-only class), use '-' for stdout")

    parser.add_argument("file", nargs="?", default=None, help="Input file (omit to use stdin)")
    args = parser.parse_args()

    input_text = sys.stdin.read() if args.file is None else read_file(args.file)
    ast = parse.parse(input_text)

    errors = typecheck.typecheck(ast)
    if errors:
        for e in errors:
            print("Error: {}".format(e))
        sys.exit(1)

    print()
    print(syntax_tools.pprint(ast))

    ast = desugar.desugar(ast)
    print(syntax_tools.pprint(ast))

    orig_ast = ast
    ast, state_map = synthesis.synthesize(ast, use_cache = not args.disable_cache)
    print()
    print(syntax_tools.pprint(ast))

    lib = library.Library()
    impls = list(autotuning.enumerate_impls(ast, lib))
    print("# impls: {}".format(len(impls)))

    impl = impls[0] # TODO: autotuning
    sharing = compute_sharing(state_map, dict(impl.statevars))

    print()
    print(impl.statevars)

    java = args.java
    if java is not None:
        with common.open_maybe_stdout(java) as out:
            out.write(compile.JavaPrinter().visit(impl, state_map, sharing, package=args.package))

    cxx = getattr(args, "c++")
    if cxx is not None:
        with common.open_maybe_stdout(cxx) as out:
            out.write(compile.CxxPrinter().visit(impl, state_map, sharing))
