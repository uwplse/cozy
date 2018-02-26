import unittest

from cozy.syntax_tools import mk_lambda, pprint, alpha_equivalent, subst, strip_EStateVar
from cozy.target_syntax import *
from cozy.cost_model import CompositeCostModel
from cozy.typecheck import retypecheck
from cozy.evaluation import Bag, mkval
from cozy.synthesis.core import instantiate_examples, fingerprint, improve
from cozy.synthesis.grammar import BinderBuilder
from cozy.solver import valid, satisfy

handle_type = THandle("H", INT)
handle1 = (1, mkval(INT))
handle2 = (2, mkval(INT))
handle3 = (3, mkval(INT))
zero = ENum(0).with_type(INT)

def check_discovery(spec, expected, state_vars=[], args=[], examples=[]):
    for r in improve(spec,
            assumptions=T,
            binders=[],
            state_vars=state_vars,
            args=args,
            cost_model=CompositeCostModel(),
            builder=BinderBuilder(args=args, state_vars=state_vars, binders=[]),
            examples=examples):
        print("GOT RESULT ==> {}".format(pprint(r)))
        if isinstance(expected, Exp):
            if alpha_equivalent(r, expected):
                return True
        elif expected(r):
            return True
    return False

class TestSynthesisCore(unittest.TestCase):

    def test_instantiate_examples_empty(self):
        bag = Bag((handle1, handle2, handle3))
        examples = [{ "x": bag }]
        binder = EVar("binder").with_type(BOOL)
        new_examples = list(instantiate_examples(examples, [binder]))
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
            return res == EStateVar(EVar("xs"))
        for r in improve(target, assumptions, [x], [xs], [], CompositeCostModel(), BinderBuilder([x], [xs], []), stop_callback=should_stop):
            print(pprint(r))
            res = r
        assert should_stop()

    def test_incomplete_binders_list(self):
        res = None
        x = EVar("x").with_type(BOOL)
        xs = EVar("xs").with_type(TBag(BOOL))
        target = EFilter(EStateVar(xs), ELambda(x, x))
        assumptions = EUnaryOp(UOp.All, xs)
        assert retypecheck(target)
        assert retypecheck(assumptions)
        def should_stop():
            return res == EStateVar(EVar("xs"))
        for r in improve(target, assumptions, [], [xs], [], CompositeCostModel(), BinderBuilder([], [xs], []), stop_callback=should_stop):
            print(pprint(r))
            res = r
        assert should_stop()

    def test_incomplete_binders_list_2(self):
        res = None
        x = EVar("x").with_type(BOOL)
        xs = EVar("xs").with_type(TBag(BOOL))
        target = EFilter(EStateVar(xs), ELambda(x, T))
        assumptions = EUnaryOp(UOp.All, xs)
        assert retypecheck(target)
        assert retypecheck(assumptions)
        def should_stop():
            return res == EStateVar(EVar("xs"))
        for r in improve(target, assumptions, [], [xs], [], CompositeCostModel(), BinderBuilder([], [xs], []), stop_callback=should_stop):
            print(pprint(r))
            res = r
        assert should_stop()

    def test_bag_plus_minus(self):
        t = THandle("H", INT)
        x = EVar("x").with_type(t)
        xs = EVar("xs").with_type(TBag(t))
        spec = EBinOp(EBinOp(xs, "+", ESingleton(x)), "-", ESingleton(x))
        expected = xs
        assert retypecheck(spec)
        assert valid(EEq(spec, expected))
        ex = satisfy(ENot(EBinOp(spec, "===", expected).with_type(BOOL)))
        assert ex is not None
        assert check_discovery(spec=spec, expected=expected, args=[x, xs], examples=[ex])

    def test_map_discovery(self):
        xs = EVar("xs").with_type(INT_BAG)
        y = EVar("y").with_type(INT)
        spec = EFilter(EStateVar(xs), mk_lambda(INT, lambda x: EEq(x, y)))
        assert retypecheck(spec)
        assert check_discovery(spec=spec, expected=lambda e: isinstance(e, EMapGet) and isinstance(e.map, EStateVar) and valid(EEq(e, spec)), args=[y], state_vars=[xs])
