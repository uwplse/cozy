import unittest

from cozy.syntax_tools import mk_lambda, pprint
from cozy.target_syntax import *
from cozy.cost_model import CompositeCostModel
from cozy.typecheck import retypecheck
from cozy.evaluation import Bag, mkval
from cozy.synthesis.core import instantiate_examples, fingerprint, improve
from cozy.synthesis.grammar import BinderBuilder

handle_type = THandle("H", INT)
handle1 = (1, mkval(INT))
handle2 = (2, mkval(INT))
handle3 = (3, mkval(INT))
zero = ENum(0).with_type(INT)

class TestSynthesisCore(unittest.TestCase):

    def test_instantiate_examples_empty(self):
        bag = Bag((handle1, handle2, handle3))
        examples = [{ "x": bag }]
        binder = EVar("binder").with_type(BOOL)
        new_examples = list(instantiate_examples((zero,), examples, [binder]))
        assert new_examples == [
            { "x": bag, "binder": False }]

    def test_easy_synth(self):
        res = None
        x = EVar("x").with_type(BOOL)
        xs = EVar("xs").with_type(TBag(BOOL))
        target = EFilter(EStateVar(xs), ELambda(x, x))
        assumptions = EUnaryOp(UOp.All, xs)
        assert retypecheck(target)
        assert retypecheck(assumptions)
        def should_stop():
            return isinstance(res, EVar)
        for r in improve(target, assumptions, [x], [xs], [], CompositeCostModel(), BinderBuilder([x], [xs], []), stop_callback=should_stop):
            print(pprint(r))
            res = r

    def test_incomplete_binders_list(self):
        res = None
        x = EVar("x").with_type(BOOL)
        xs = EVar("xs").with_type(TBag(BOOL))
        target = EFilter(EStateVar(xs), ELambda(x, x))
        assumptions = EUnaryOp(UOp.All, xs)
        assert retypecheck(target)
        assert retypecheck(assumptions)
        def should_stop():
            return isinstance(res, EVar)
        for r in improve(target, assumptions, [], [xs], [], CompositeCostModel(), BinderBuilder([], [xs], []), stop_callback=should_stop):
            print(pprint(r))
            res = r

    def test_incomplete_binders_list_2(self):
        res = None
        x = EVar("x").with_type(BOOL)
        xs = EVar("xs").with_type(TBag(BOOL))
        target = EFilter(EStateVar(xs), ELambda(x, T))
        assumptions = EUnaryOp(UOp.All, xs)
        assert retypecheck(target)
        assert retypecheck(assumptions)
        def should_stop():
            return isinstance(res, EVar)
        for r in improve(target, assumptions, [], [xs], [], CompositeCostModel(), BinderBuilder([], [xs], []), stop_callback=should_stop):
            print(pprint(r))
            res = r
