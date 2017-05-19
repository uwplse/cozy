#!/usr/bin/env python

"""
Main entry point for synthesis. Run with --help for options.
"""

import sys
import argparse
import datetime

from cozy import parse
from cozy import compile
from cozy import common
from cozy import typecheck
from cozy import desugar
from cozy import target_syntax
from cozy import syntax_tools
from cozy import invariant_preservation
from cozy import synthesis
from cozy import library
from cozy import autotuning
from cozy import sharing
from cozy import opts

save_failed_codegen_inputs = opts.Option("save-failed-codegen-inputs", str, "/tmp/failed_codegen.py", metavar="PATH")

def run():
    parser = argparse.ArgumentParser(description='Data structure synthesizer.')
    parser.add_argument("-t", "--timeout", metavar="N", type=float, default=60, help="Per-query synthesis timeout (in seconds); default=60")
    parser.add_argument("-s", "--simple", action="store_true", help="Do not synthesize improved solution; use the most trivial implementation of the spec")

    java_opts = parser.add_argument_group("Java codegen")
    java_opts.add_argument("--java", metavar="FILE.java", default=None, help="Output file for java classes, use '-' for stdout")
    java_opts.add_argument("--package", metavar="pkg.name", default=None, help="Java package name")

    cxx_opts = parser.add_argument_group("C++ codegen")
    cxx_opts.add_argument("--c++", metavar="FILE.h", default=None, help="Output file for C++ (header-only class), use '-' for stdout")

    internal_opts = parser.add_argument_group("Internal parameters")
    opts.setup(internal_opts)

    parser.add_argument("file", nargs="?", default=None, help="Input file (omit to use stdin)")
    args = parser.parse_args()
    opts.read(args)

    input_text = sys.stdin.read() if args.file is None else common.read_file(args.file)
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

    errors = invariant_preservation.check_ops_preserve_invariants(ast)
    if errors:
        for e in errors:
            print("Error: {}".format(e))
        sys.exit(1)

    if not args.simple:
        ast, state_map = synthesis.synthesize(
            ast,
            per_query_timeout = datetime.timedelta(seconds=args.timeout))
        print()
        print(syntax_tools.pprint(ast))
    else:
        state_map = { v : target_syntax.EVar(v).with_type(t) for (v, t) in ast.statevars }

    lib = library.Library()
    impls = list(autotuning.enumerate_impls(ast, lib))
    print("# impls: {}".format(len(impls)))

    impl = impls[0] # TODO: autotuning
    share_info = sharing.compute_sharing(state_map, dict(impl.statevars))

    print()
    print(impl.statevars)

    try:
        java = args.java
        if java is not None:
            with common.open_maybe_stdout(java) as out:
                out.write(compile.JavaPrinter().visit(impl, state_map, share_info, package=args.package))

        cxx = getattr(args, "c++")
        if cxx is not None:
            with common.open_maybe_stdout(cxx) as out:
                out.write(compile.CxxPrinter().visit(impl, state_map, share_info))
    except:
        print("Code generation failed!")
        if save_failed_codegen_inputs.value:
            with open(save_failed_codegen_inputs.value, "w") as f:
                f.write("impl = {}\n".format(repr(impl)))
                f.write("state_map = {}\n".format(repr(state_map)))
                f.write("share_info = {}\n".format(repr(share_info)))
            print("Implementation was dumped to {}".format(save_failed_codegen_inputs.value))
        raise
