import unittest
import datetime

from cozy.common import save_property
from cozy.syntax_tools import mk_lambda, pprint, alpha_equivalent, deep_copy
from cozy.target_syntax import *
from cozy.contexts import RootCtx, UnderBinder
from cozy.typecheck import retypecheck, typecheck
from cozy.evaluation import mkval
from cozy.cost_model import CostModel
from cozy.synthesis import construct_initial_implementation, improve_implementation
from cozy.synthesis.core import improve, allow_random_assignment_heuristic
from cozy.synthesis.enumeration import Enumerator, Fingerprint
from cozy.parse import parse_spec
from cozy.solver import valid, satisfy
from cozy.pools import RUNTIME_POOL, STATE_POOL
from cozy.desugar import desugar
from cozy.value_types import Bag
from cozy.structures.heaps import EMakeMinHeap, EMakeMaxHeap, EHeapPeek, EHeapPeek2
from cozy.synthesis.acceleration import accelerate

handle_type = THandle("H", INT)
handle1 = (1, mkval(INT))
handle2 = (2, mkval(INT))
handle3 = (3, mkval(INT))
zero = ENum(0).with_type(INT)

def check_discovery(spec, expected, state_vars=[], args=[], examples=[], assumptions=ETRUE):
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
        with save_property(allow_random_assignment_heuristic, "value"):
            allow_random_assignment_heuristic.value = False
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


class TestEnumeration(unittest.TestCase):

    def test_fingerprint_equality(self):
        inp = { "x": 1 }
        e1 = EVar("x").with_type(INT)
        e2 = ONE
        fp1 = Fingerprint.of(e1, [inp])
        fp2 = Fingerprint.of(e2, [inp])
        self.assertEqual(hash(fp1), hash(fp2))
        self.assertEqual(len(fp1), len(fp2))
        self.assertEqual(fp1, fp2)
        self.assertNotEqual(fp1, 1)

    def test_fingerprint_subset(self):
        inp = { "x": Bag([1]) }
        e1 = EVar("x").with_type(INT_BAG)
        e2 = EEmptyList().with_type(e1.type)
        fp1 = Fingerprint.of(e1, [inp])
        fp2 = Fingerprint.of(e2, [inp])
        self.assertNotEqual(fp1, fp2)
        assert not fp1.subset_of(fp2)
        assert fp2.subset_of(fp1)

    def test_state_pool_boundary(self):
        """
        When enumerating expressions, we shouldn't ever enumerate state
        expressions in a context where some binders are runtime variables.
        """

        class TestEnumerator(Enumerator):

            def __init__(self, *args, **kwargs):
                super().__init__(*args, **kwargs)
                self.state_enumerations = 0

            def _enumerate_core(self, context, size, pool):
                print("_enumerate_core({}, {}, {})".format(context, size, pool))
                if pool == STATE_POOL:
                    self.state_enumerations += 1
                return super()._enumerate_core(context, size, pool)

        state_bag = EVar("state").with_type(INT_BAG)
        context = RootCtx(
            state_vars=[state_bag],
            args=[EVar("arg").with_type(INT)])

        enumerator = TestEnumerator(
            examples=[
                {"state": Bag([10]), "arg": 10},
                {"state": Bag([20]), "arg": 30}],
            cost_model=CostModel())

        for e in enumerator.enumerate(context, 1, RUNTIME_POOL):
            pass

        for e in enumerator.enumerate(
                UnderBinder(context, EVar("x").with_type(INT), EStateVar(state_bag).with_type(state_bag.type), RUNTIME_POOL),
                1,
                RUNTIME_POOL):
            pass

        assert enumerator.state_enumerations == 1

    def test_hint_instantation(self):

        x = EVar("x").with_type(INT)
        y = EVar("y").with_type(INT)
        z = EVar("z").with_type(INT)
        hint = ECall("f", (x,)).with_type(INT)
        context = UnderBinder(
            RootCtx(args=[x]),
            v=y,
            bag=ESingleton(x).with_type(TBag(x.type)),
            bag_pool=RUNTIME_POOL)
        cost_model = CostModel()

        f = lambda a: a + 1
        enumerator = Enumerator(
            examples=[{"x": 1, "f": f}, {"x": 100, "f": f}],
            hints=[(hint, context, RUNTIME_POOL)],
            cost_model=cost_model)

        results = []
        for ctx in (
                context,
                context.parent(),
                UnderBinder(context, v=z, bag=ESingleton(y).with_type(TBag(y.type)), bag_pool=RUNTIME_POOL),
                UnderBinder(context.parent(), v=z, bag=ESingleton(x).with_type(TBag(y.type)), bag_pool=RUNTIME_POOL),
                UnderBinder(context.parent(), v=y, bag=ESingleton(ONE).with_type(INT_BAG), bag_pool=RUNTIME_POOL)):
            print("-" * 30)
            found = False
            for e in enumerator.enumerate(ctx, 0, RUNTIME_POOL):
                print(" -> {}".format(pprint(e)))
                found = found or alpha_equivalent(e, hint)
            print("found? {}".format(found))
            results.append(found)

        assert all(results)

    def test_heap_enumeration(self):
        xs = EVar("xs").with_type(INT_BAG)
        context = RootCtx(state_vars=[xs])
        cost_model = CostModel()

        def not_min_or_max(e, *args, **kwargs):
            # forbid min/max to ensure that heap operations get cached
            if isinstance(e, EArgMin) or isinstance(e, EArgMax):
                return False
            return True

        enumerator = Enumerator(
            examples=[{"xs": Bag(())}, {"xs": Bag((1,2))}, {"xs": Bag((1,1))}],
            cost_model=cost_model,
            check_wf=not_min_or_max)

        with save_property(accelerate, "value"):
            accelerate.value = False

            print("-" * 20 + " Looking for xs...")
            found_xs = False
            for e in enumerator.enumerate(context, 0, STATE_POOL):
                print(pprint(e))
                if e == xs:
                    assert retypecheck(deep_copy(e))
                    found_xs = True
                    print("^^^ FOUND")
            assert found_xs

            print("-" * 20 + " Looking for heap construction...")
            found_make_heap = False
            for e in enumerator.enumerate(context, 1, STATE_POOL):
                print(pprint(e))
                if isinstance(e, EMakeMinHeap) or isinstance(e, EMakeMaxHeap):
                    assert retypecheck(deep_copy(e))
                    found_make_heap = True
                    print("^^^ FOUND")
            assert found_make_heap

            print("-" * 20 + " Looking for heap usage...")
            found_heap_peek = False
            for e in enumerator.enumerate(context, 2, RUNTIME_POOL):
                print(pprint(e))
                if isinstance(e, EHeapPeek) or isinstance(e, EHeapPeek2):
                    assert retypecheck(deep_copy(e))
                    found_heap_peek = True
                    print("^^^ FOUND")
            assert found_heap_peek

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

        assert len(impl.concretization_functions) == 1
        (v, e), = list(impl.concretization_functions.items())
        print("{} = {}".format(v, pprint(e)))
        assert e.type == BOOL
