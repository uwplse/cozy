import os
import unittest

from cozy.target_syntax import *
from cozy.parse import parse
from cozy.typecheck import typecheck
from cozy import syntax

class TestSpecs(unittest.TestCase):
    pass

files = [
    "agg",
    "basic",
    "clausedb",
    "func",
    "graph",
    "intset",
    "disjunction",
    "map",
    "nested-map",
    "in",
    "polyupdate",
    "read-after-write",
    "boundsbug2",
    "docstring"]

for filename in files:
    def setup(filename):

        def f(self):
            with open(os.path.join("specs", filename + ".ds"), "r") as f:
                ast = parse(f.read())
            assert isinstance(ast, Spec)

            errs = typecheck(ast)
            for e in errs:
                print(e)
            assert not errs

        f.__name__ = "test_{}".format(filename.replace("-", "_"))
        setattr(TestSpecs, f.__name__, f)
    setup(filename)

class TestParser(unittest.TestCase):
    def test_parse_len_old(self):
        sample = """
        In:
            state foo : Bag<Int>
            query fooLen()
                sum [1 | _ <- foo]
        """
        parse(sample)

    def test_parse_len(self):
        sample = """
        In:
            state foo : Bag<Int>
            query fooLen()
                len foo
        """
        parse(sample)

    def test_parse_method_call_with_expr(self):
        sample = """
        Test:
            state foo : Bag<Int>
            op add2x(i : Int)
                foo.add(i + i);
            op add3x(i : Int)
                foo.add(i + i + i);
            op addIncremented(i : Int)
                foo.add(i + 1);
            op addNegative(i : Int)
                foo.add(0 - i);
        """
        parse(sample)

    def test_guard_mechanism(self):
        sample = """
        Test:
            state foo : Bag<Int>
            op add_2x_unique(i : Int)
                if not (i + i) in foo {
                    foo.add(i + i);
                }
        """
        parse(sample)

    def test_dangling_else(self):
        sample = """Test:
           state f : Bag<Int>
           op foo(i : Int)
                if not (i in foo) {
                    if not ((i + i) in foo) {
                        foo.add(i + i + i);
                    } else {
                        foo.add(i + i + i + i);
                    }
                }
        """
        # Verify that `else` code pairs with inner `if`.
        ast = parse(sample)
        foo = ast.methods[0]
        assert isinstance(foo.body, syntax.SIf)
        assert isinstance(foo.body.then_branch.else_branch, syntax.SCall)
        assert isinstance(foo.body.else_branch, syntax.SNoOp)
