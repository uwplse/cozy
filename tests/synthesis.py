import unittest

from cozy.syntax_tools import mk_lambda
from cozy.target_syntax import *
from cozy.typecheck import INT, BOOL
from cozy.evaluation import Bag, mkval
from cozy.synthesis.core import instantiate_examples, values_of_type, fingerprint

handle_type = THandle("H", INT)
handle1 = (1, mkval(INT))
handle2 = (2, mkval(INT))
handle3 = (3, mkval(INT))

class TestSynthesisCore(unittest.TestCase):

    def test_values_of_type(self):
        v = Bag((handle1, handle2, handle3))
        vals = list(values_of_type(v, TBag(handle_type), handle_type))
        assert vals == [handle1, handle2, handle3], "vals={}".format(repr(vals))

    def test_instantiate_examples(self):
        bag = Bag((handle1, handle2, handle3))
        examples = [{ "x": bag }]
        vars = [EVar("x").with_type(TBag(handle_type))]
        binder = EVar("binder").with_type(handle_type)
        new_examples = list(instantiate_examples(examples, vars, [binder]))
        assert new_examples == [
            { "x": bag, "binder": handle1 },
            { "x": bag, "binder": handle2 },
            { "x": bag, "binder": handle3 }], "new_examples={}".format(repr(new_examples))

    def test_instantiate_examples_empty(self):
        bag = Bag((handle1, handle2, handle3))
        examples = [{ "x": bag }]
        vars = [EVar("x").with_type(TBag(handle_type))]
        binder = EVar("binder").with_type(BOOL)
        new_examples = list(instantiate_examples(examples, vars, [binder]))
        assert new_examples == [
            { "x": bag, "binder": False }]

    def test_fingerprint(self):
        bag = Bag((handle1, handle2, handle3))
        examples = [{ "x": bag }]
        vars = [EVar("x").with_type(TBag(handle_type))]
        binder = EVar("binder").with_type(handle_type)
        otherbinder = EVar("otherbinder").with_type(BOOL)
        examples = instantiate_examples(examples, vars, [binder, otherbinder])
        fp = fingerprint(binder, examples, vars, [binder, otherbinder])
        print("fp = {}".format(fp))
        assert len(fp) > 1
