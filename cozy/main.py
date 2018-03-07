#!/usr/bin/env python

"""
Main entry point for synthesis. Run with --help for options.
"""

from collections import defaultdict
import sys
import argparse
import datetime
import pickle

from cozy import syntax
from cozy import parse
from cozy import codegen
from cozy import common
from cozy import typecheck
from cozy import desugar
from cozy import syntax_tools
from cozy import handle_tools
from cozy import invariant_preservation
from cozy import synthesis
from cozy import library
from cozy import autotuning
from cozy import sharing
from cozy import opts

save_failed_codegen_inputs = opts.Option("save-failed-codegen-inputs", str, "/tmp/failed_codegen.py", metavar="PATH")
enable_autotuning = opts.Option("enable-autotuning", bool, False)
checkpoint_prefix = opts.Option("checkpoint-prefix", str, "")

def run():
    parser = argparse.ArgumentParser(description='Data structure synthesizer.')
    parser.add_argument("-S", "--save", metavar="FILE", type=str, default=None, help="Save synthesis output")
    parser.add_argument("-R", "--resume", action="store_true", help="Resume from saved synthesis output")
    parser.add_argument("-t", "--timeout", metavar="N", type=float, default=60, help="Per-query synthesis timeout (in seconds); default=60")
    parser.add_argument("-s", "--simple", action="store_true", help="Do not synthesize improved solution; use the most trivial implementation of the spec")
    parser.add_argument("-p", "--port", metavar="P", type=int, default=None, help="Port to run progress-showing HTTP server")

    java_opts = parser.add_argument_group("Java codegen")
    java_opts.add_argument("--java", metavar="FILE.java", default=None, help="Output file for java classes, use '-' for stdout")
    java_opts.add_argument("--unboxed", action="store_true", help="Use unboxed primitives. NOTE: synthesized data structures may require GNU Trove (http://trove.starlight-systems.com/)")

    cxx_opts = parser.add_argument_group("C++ codegen")
    cxx_opts.add_argument("--c++", metavar="FILE.h", default=None, help="Output file for C++ (header-only class), use '-' for stdout")
    cxx_opts.add_argument("--use-qhash", action="store_true", help="QHash---the Qt implementation of hash maps---often outperforms the default C++ map implementations")

    internal_opts = parser.add_argument_group("Internal parameters")
    opts.setup(internal_opts)

    parser.add_argument("file", nargs="?", default=None, help="Input file (omit to use stdin)")
    args = parser.parse_args()
    opts.read(args)

    if args.resume:
        if args.file is None:
            ast = pickle.load(sys.stdin.buffer)
        else:
            with open(args.file, "rb") as f:
                ast = pickle.load(f)
        print("Loaded implementation from {}".format("stdin" if args.file is None else "file {}".format(args.file)))
    else:
        input_text = sys.stdin.read() if args.file is None else common.read_file(args.file)
        ast = parse.parse(input_text)

        errors = typecheck.typecheck(ast)
        if errors:
            for e in errors:
                print("Error: {}".format(e))
            sys.exit(1)

        # print()
        # print(syntax_tools.pprint(ast))

        ast = desugar.desugar(ast)
        ast = invariant_preservation.add_implicit_handle_assumptions(ast)
        # print(syntax_tools.pprint(ast))

        print("Checking assumptions...")
        errors = (
            invariant_preservation.check_ops_preserve_invariants(ast) +
            invariant_preservation.check_the_wf(ast))
        if errors:
            for e in errors:
                print("Error: {}".format(e))
            sys.exit(1)
        print("Done!")

        ast = synthesis.construct_initial_implementation(ast)

    start = datetime.datetime.now()
    if not args.simple:
        callback = None
        server = None
        if checkpoint_prefix.value:
            def callback(res):
                impl, ast, state_map = res
                assert isinstance(impl, synthesis.Implementation)
                now = datetime.datetime.now()
                elapsed = now - start
                fname = "{}{:010d}.synthesized".format(checkpoint_prefix.value, int(elapsed.total_seconds()))
                with open(fname, "wb") as f:
                    pickle.dump(impl, f)
                    print("Saved checkpoint {}".format(fname))

        if args.port:
            from cozy import progress_server
            state = ["Initializing..."]
            orig_callback = callback
            def callback(res):
                if orig_callback is not None:
                    orig_callback(res)
                impl, ast, state_map = res
                s = "<!DOCTYPE html>\n"
                s += "<html>"
                s += "<head><style>"
                s += ".kw { color: #909; font-weight: bold; }"
                s += ".builtin { color: #009; font-weight: bold; }"
                s += ".comment { color: #999; }"
                s += "</style></head>"
                s += "<body><pre>"
                for v, e in state_map.items():
                    s += "{} : {} = {}\n".format(v, syntax_tools.pprint(e.type, format="html"), syntax_tools.pprint(e, format="html"))
                s += "\n"
                s += syntax_tools.pprint(ast, format="html")
                s += "</pre></body></html>"
                state[0] = s
            server = progress_server.ProgressServer(port=args.port, callback=lambda: state[0])
            server.start_async()
        ast = synthesis.improve_implementation(
            ast,
            timeout           = datetime.timedelta(seconds=args.timeout),
            progress_callback = callback)
        if server is not None:
            server.join()

    print("Generating IR...")
    code = ast.code
    print("Loading concretization functions...")
    state_map = ast.concretization_functions
    print()
    for v, e in state_map.items():
        print("{} : {} = {}".format(v, syntax_tools.pprint(e.type), syntax_tools.pprint(e)))
    print()
    print(syntax_tools.pprint(code))

    if args.save:
        with open(args.save, "wb") as f:
            pickle.dump(ast, f)
            print("Saved implementation to file {}".format(args.save))

    if enable_autotuning.value:
        print("Generating final concrete implementation...")
        lib = library.Library()
        impls = list(autotuning.enumerate_impls(code, state_map, lib, assumptions=ast.spec.assumptions))
        print("# impls: {}".format(len(impls)))

        impl = impls[0] # TODO: autotuning
        for (v, t) in impl.statevars:
            print("{} ~~> {}".format(v, syntax_tools.pprint(t)))
        share_info = sharing.compute_sharing(state_map, dict(impl.statevars))

        print()
        print(impl.statevars)
    else:
        impl = code
        share_info = defaultdict(list)

    print("Fixing EWithAlteredValue...")
    impl = syntax_tools.shallow_copy(impl)
    impl.methods = tuple(
        syntax_tools.rewrite_ret(m, handle_tools.fix_ewithalteredvalue) if isinstance(m, syntax.Query) else m
        for m in impl.methods)
    print("Done!")

    try:
        java = args.java
        if java is not None:
            with common.open_maybe_stdout(java) as out:
                out.write(codegen.JavaPrinter(boxed=(not args.unboxed)).visit(impl, state_map, share_info, abstract_state=ast.spec.statevars))

        cxx = getattr(args, "c++")
        if cxx is not None:
            with common.open_maybe_stdout(cxx) as out:
                out.write(codegen.CxxPrinter(use_qhash=args.use_qhash).visit(impl, state_map, share_info, abstract_state=ast.spec.statevars))
    except:
        print("Code generation failed!")
        if save_failed_codegen_inputs.value:
            with open(save_failed_codegen_inputs.value, "w") as f:
                f.write("impl = {}\n".format(repr(impl)))
                f.write("state_map = {}\n".format(repr(state_map)))
                f.write("share_info = {}\n".format(repr(share_info)))
            print("Implementation was dumped to {}".format(save_failed_codegen_inputs.value))
        raise
