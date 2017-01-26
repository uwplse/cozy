import os
import unittest

from cozy.target_syntax import *
from cozy.parse import parse

class TestParser(unittest.TestCase):
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
    "in"]

for filename in files:
    def setup(filename):
        def f(self):
            with open(os.path.join("specs", filename + ".ds"), "r") as f:
                ast = parse(f.read())
            assert isinstance(ast, Spec)
        f.__name__ = "test_{}".format(filename.replace("-", "_"))
        setattr(TestParser, f.__name__, f)
    setup(filename)
