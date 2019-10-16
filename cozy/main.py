#!/usr/bin/env python

"""
Main entry point for Cozy synthesis. Run with --help for options.
"""

from collections import defaultdict
import sys
import argparse
import datetime
import pickle

from multiprocessing import Value

from cozy import parse
from cozy import codegen
from cozy import common
from cozy import typecheck
from cozy import desugar
from cozy import syntax_tools
from cozy import invariant_preservation
from cozy import synthesis
from cozy.structures import rewriting
from cozy import opts

save_failed_codegen_inputs = opts.Option("save-failed-codegen-inputs", str, "/tmp/failed_codegen.py", metavar="PATH")
checkpoint_prefix = opts.Option("checkpoint-prefix", str, "")
do_cse = opts.Option("cse", bool, False, description="Perform common subexpression elimination just before codegen")

def run():
    """Entry point for Cozy executable.

    This procedure reads sys.argv and executes the requested tasks.
    """

    parser = argparse.ArgumentParser(description='Data structure synthesizer.')
    parser.add_argument("-S", "--save", metavar="FILE", type=str, default=None, help="Save synthesis output")
    parser.add_argument("-R", "--resume", action="store_true", help="Resume from saved synthesis output")
    parser.add_argument("-t", "--timeout", metavar="N", type=float, default=60,
                        help="Global synthesis timeout (in seconds); default=60. " +
                             "Smaller timeout speeds up the synthesis process, but may also result in less efficient code")
    parser.add_argument("-s", "--simple", action="store_true", help="Do not synthesize improved solution; use the most trivial implementation of the spec")
    parser.add_argument("-p", "--port", metavar="P", type=int, default=None, help="Port to run progress-showing HTTP server")

    java_opts = parser.add_argument_group("Java codegen")
    java_opts.add_argument("--java", metavar="FILE.java", default=None, help="Output file for java classes, use '-' for stdout")
    java_opts.add_argument("--unboxed", action="store_true", help="Use unboxed primitives. NOTE: synthesized data structures may require GNU Trove (http://trove.starlight-systems.com/)")

    cxx_opts = parser.add_argument_group("C++ codegen")
    cxx_opts.add_argument("--c++", metavar="FILE.h", default=None, help="Output file for C++ (header-only class), use '-' for stdout")
    cxx_opts.add_argument("--use-qhash", action="store_true", help="QHash---the Qt implementation of hash maps---often outperforms the default C++ map implementations")

    ruby_opts = parser.add_argument_group("Ruby codegen")
    ruby_opts.add_argument("--ruby", metavar="FILE.rb", default=None, help="Output file for Ruby, use '-' for stdout")

    internal_opts = parser.add_argument_group("Internal parameters")
    opts.setup(internal_opts)

    parser.add_argument("file", nargs="?", default=None, help="Input file (omit to use stdin)")
    args = parser.parse_args()
    opts.read(args)

    improve_count = Value('i', 0)

    if args.resume:
        with common.open_maybe_stdin(args.file or "-", mode="rb") as f:
            ast = pickle.load(f)
        print("Loaded implementation from {}".format("stdin" if args.file is None else "file {}".format(args.file)))
    else:
        with common.open_maybe_stdin(args.file or "-") as f:
            input_text = f.read()
        ast = parse.parse_spec(input_text)

        # Collection of errors in user-provided specification
        errors = typecheck.typecheck(ast)
        if errors:
            for e in errors:
                print("Error: {}".format(e))
            sys.exit(1)

        ast = desugar.desugar(ast)
        ast = invariant_preservation.add_implicit_handle_assumptions(ast)

        print("Checking call legality...")
        call_errors = invariant_preservation.check_calls_wf(ast)
        ast = syntax_tools.inline_calls(ast)

        print("Checking invariant preservation...")
        errors = (
            invariant_preservation.check_ops_preserve_invariants(ast) +
            invariant_preservation.check_the_wf(ast) +
            invariant_preservation.check_minmax_wf(ast) +
            call_errors)
        if errors:
            for e in errors:
                print("Error: {}".format(e))
            sys.exit(1)
        print("Done!")

        ast = synthesis.construct_initial_implementation(ast)

    start = datetime.datetime.now()

    if args.simple:
        if args.save:
            with open(args.save, "wb") as f:
                pickle.dump(ast, f)
                print("Saved implementation to file {}".format(args.save))
    else:
        callback = None
        server = None

        if checkpoint_prefix.value:
            def callback(impl):
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
            def callback(impl):
                if orig_callback is not None:
                    orig_callback(impl)
                ast = impl.code
                state_map = impl.concretization_functions
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

        # Do full synthesis
        ast = synthesis.improve_implementation(
            ast,
            timeout           = datetime.timedelta(seconds=args.timeout),
            progress_callback = callback,
            improve_count=improve_count,
            save=args.save)

        if server is not None:
            server.join()

    print("Generating IR...")
    code = ast.code

    print("Inlining calls...")
    code = syntax_tools.inline_calls(code)

    print("Generating code for extension types...")
    code, state_map = rewriting.rewrite_extensions(code, ast.concretization_functions)

    if do_cse.value:
        print("Eliminating common subexpressions...")
        code = syntax_tools.cse_replace_spec(code)

    print("Concretization functions:")
    print()
    for v, e in state_map.items():
        print("{} : {} = {}".format(v, syntax_tools.pprint(e.type), syntax_tools.pprint(e)))
    print()
    print(syntax_tools.pprint(code))

    impl = code
    share_info = defaultdict(list)

    try:
        java = args.java
        if java is not None:
            with common.open_maybe_stdout(java) as out:
                codegen.JavaPrinter(out=out, boxed=(not args.unboxed)).visit(impl, state_map, share_info, abstract_state=ast.spec.statevars)

        cxx = getattr(args, "c++")
        if cxx is not None:
            with common.open_maybe_stdout(cxx) as out:
                codegen.CxxPrinter(out=out, use_qhash=args.use_qhash).visit(impl, state_map, share_info, abstract_state=ast.spec.statevars)

        ruby = args.ruby
        if ruby is not None:
            with common.open_maybe_stdout(ruby) as out:
                codegen.RubyPrinter(out=out).visit(impl, state_map, share_info, abstract_state=ast.spec.statevars)
    except:
        print("Code generation failed!")
        if save_failed_codegen_inputs.value:
            with open(save_failed_codegen_inputs.value, "w") as f:
                f.write("impl = {}\n".format(repr(impl)))
                f.write("state_map = {}\n".format(repr(state_map)))
                f.write("share_info = {}\n".format(repr(share_info)))
            print("Implementation was dumped to {}".format(save_failed_codegen_inputs.value))
        raise

    print("Number of improvements done: {}".format(improve_count.value))
