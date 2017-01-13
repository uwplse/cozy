import unittest

from cozy.syntax_tools import mk_lambda
from cozy.target_syntax import *
from cozy.typecheck import INT, BOOL
from cozy.evaluation import Bag
from cozy.synthesis.core import instantiate_examples, values_of_type, fingerprint

class TestSynthesisCore(unittest.TestCase):

    def test_values_of_type(self):
        v = Bag((1, 2, 3))
        assert list(values_of_type(v, TBag(INT), INT)) == [1, 2, 3]

    def test_instantiate_examples(self):
        bag = Bag((1, 2, 3))
        examples = [{ "x": bag }]
        vars = [EVar("x").with_type(TBag(INT))]
        binder = EVar("binder").with_type(INT)
        new_examples = list(instantiate_examples(examples, vars, binder))
        assert new_examples == [
            { "x": bag, "binder": 1 },
            { "x": bag, "binder": 2 },
            { "x": bag, "binder": 3 }]

    def test_instantiate_examples_empty(self):
        bag = Bag((1, 2, 3))
        examples = [{ "x": bag }]
        vars = [EVar("x").with_type(TBag(INT))]
        binder = EVar("binder").with_type(BOOL)
        new_examples = list(instantiate_examples(examples, vars, binder))
        assert new_examples == [
            { "x": bag, "binder": False }]

    def test_fingerprint(self):
        bag = Bag((1, 2, 3))
        examples = [{ "x": bag }]
        vars = [EVar("x").with_type(TBag(INT))]
        binder = EVar("binder").with_type(INT)
        otherbinder = EVar("otherbinder").with_type(BOOL)
        fp = fingerprint(binder, examples, vars, [binder, otherbinder])
        print("fp = {}".format(fp))
        assert len(fp) > 1
