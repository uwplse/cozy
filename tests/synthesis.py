import unittest
import datetime

from cozy.syntax_tools import mk_lambda, pprint, alpha_equivalent
from cozy.target_syntax import *
from cozy.contexts import RootCtx, UnderBinder
from cozy.typecheck import retypecheck, typecheck
from cozy.evaluation import mkval
from cozy.cost_model import CostModel
from cozy.synthesis import construct_initial_implementation, improve_implementation
from cozy.synthesis.core import improve
from cozy.synthesis.enumeration import Enumerator
from cozy.parse import parse_spec
from cozy.solver import valid, satisfy
from cozy.pools import RUNTIME_POOL
from cozy.desugar import desugar

handle_type = THandle("H", INT)
handle1 = (1, mkval(INT))
handle2 = (2, mkval(INT))
handle3 = (3, mkval(INT))
zero = ENum(0).with_type(INT)

def check_discovery(spec, expected, state_vars=[], args=[], examples=[], assumptions=T):
    ctx = RootCtx(state_vars=state_vars, args=args)
    for r in improve(spec,
            assumptions=assumptions,
            context=ctx,
            examples=examples):
        print("GOT RESULT ==> {}".format(pprint(r)))
        if isinstance(expected, Exp):
            if alpha_equivalent(r, expected):
                return True
        elif expected(r):
            return True
    return False

class TestSynthesisCore(unittest.TestCase):

    def test_easy_synth(self):
        res = None
        x = EVar("x").with_type(BOOL)
        xs = EVar("xs").with_type(TBag(BOOL))
        target = EFilter(EStateVar(xs), ELambda(x, x))
        assumptions = EUnaryOp(UOp.All, xs)
        assert retypecheck(target)
        assert retypecheck(assumptions)
        assert check_discovery(target, EStateVar(EVar("xs")), args=[x], state_vars=[xs], assumptions=assumptions)

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

    def test_map_discovery2(self):
        xs = EVar("xs").with_type(INT_BAG)
        y = EVar("y").with_type(INT)
        spec = EIn(y, EStateVar(xs))
        assert retypecheck(spec)
        assert check_discovery(spec=spec, expected=lambda e: (isinstance(e, EMapGet) or isinstance(e, EHasKey)) and isinstance(e.map, EStateVar) and valid(EEq(e, spec)), args=[y], state_vars=[xs])

    def test_let_discovery(self):
        x = EVar("x").with_type(INT)
        spec = ESum([x, x, x, x])
        assert retypecheck(spec)
        y = EVar("y").with_type(INT)
        goal = ELet(ESum([x, x]), ELambda(y, ESum([y, y])))
        assert retypecheck(goal)
        assert check_discovery(spec=spec, args=[x], expected=goal)

    def test_enumerator_fingerprints(self):
        """
        The enumerator should always give us fingerprints in the context we
        asked for.
        """
        x = EVar("x").with_type(INT)
        ctx = RootCtx(args=(x,), state_vars=())
        enumerator = Enumerator(
            examples=[{"x":0}, {"x":1}],
            cost_model=CostModel())
        inner_ctx = UnderBinder(
            ctx,
            EVar("y").with_type(INT),
            EBinOp(ESingleton(ZERO).with_type(INT_BAG), "+", ESingleton(ONE).with_type(INT_BAG)).with_type(INT_BAG),
            RUNTIME_POOL)
        fingerprint_lens = set()
        for info in enumerator.enumerate_with_info(inner_ctx, 0, RUNTIME_POOL):
            fingerprint_lens.add(len(info.fingerprint))
            print(info)
        assert len(fingerprint_lens) == 1, fingerprint_lens

class TestSpecificationSynthesis(unittest.TestCase):

    def test_bag_elimination(self):
        spec = """
            MyDataStructure:

                state elements : Bag<Int>

                query containsZero()
                    exists [x | x <- elements, x == 0]

                op addElement(x : Int)
                    elements.add(x);
        """

        spec = parse_spec(spec)
        errs = typecheck(spec)
        assert not errs, str(errs)
        spec = desugar(spec)

        impl = construct_initial_implementation(spec)
        impl = improve_implementation(impl, timeout=datetime.timedelta(seconds=30))

        print(pprint(impl.code))

        assert len(impl.concrete_state) == 1
        (v, e), = impl.concrete_state
        print("{} = {}".format(pprint(v), pprint(e)))
        assert v.type == BOOL
