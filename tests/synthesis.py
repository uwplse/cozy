import unittest

from cozy.syntax_tools import mk_lambda
from cozy.target_syntax import *
from cozy.typecheck import INT, BOOL
from cozy.evaluation import Bag, mkval
from cozy.synthesis.core import instantiate_examples, fingerprint

handle_type = THandle("H", INT)
handle1 = (1, mkval(INT))
handle2 = (2, mkval(INT))
handle3 = (3, mkval(INT))
zero = ENum(0).with_type(INT)

class TestSynthesisCore(unittest.TestCase):

    def test_instantiate_examples(self):
        bag = Bag((handle1, handle2, handle3))
        examples = [{ "x": bag }]
        vars = [EVar("x").with_type(TBag(handle_type))]
        binder = EVar("binder").with_type(handle_type)
        target = EFilter(vars[0], ELambda(binder, T)).with_type(vars[0].type)
        new_examples = list(instantiate_examples((target,), examples, vars, [binder]))
        assert new_examples == [
            { "x": bag, "binder": handle1 },
            { "x": bag, "binder": handle2 },
            { "x": bag, "binder": handle3 }], "new_examples={}".format(repr(new_examples))

    def test_instantiate_examples_empty(self):
        bag = Bag((handle1, handle2, handle3))
        examples = [{ "x": bag }]
        vars = [EVar("x").with_type(TBag(handle_type))]
        binder = EVar("binder").with_type(BOOL)
        new_examples = list(instantiate_examples((zero,), examples, vars, [binder]))
        assert new_examples == [
            { "x": bag, "binder": False }]
