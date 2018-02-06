import unittest

from cozy.target_syntax import *
from cozy.syntax_tools import mk_lambda, pprint, fresh_var, free_vars
from cozy.typecheck import retypecheck
from cozy.solver import satisfy, valid
from cozy.evaluation import eval, construct_value

class SemanticsTests(unittest.TestCase):

    """
    Tests for a few equivalences we expect to be true.
    """

    def assert_same(self, e1, e2):
        def dbg(model):
            print("model: {!r}".format(model))
            r1 = eval(e1, model)
            r2 = eval(e2, model)
            print("e1: {}".format(pprint(e1)))
            print(" ---> {!r}".format(r1))
            print("e2: {}".format(pprint(e2)))
            print(" ---> {!r}".format(r2))
        assert valid(EBinOp(e1, "===", e2).with_type(BOOL), model_callback=dbg)

    def test_distinct_mapkeys(self):
        xs = EVar("xs").with_type(INT_BAG)
        x = EVar("x").with_type(INT)
        e1 = EUnaryOp(UOp.Distinct, xs)
        e2 = EMapKeys(EMakeMap2(xs, ELambda(x, T)))
        assert retypecheck(e1)
        assert retypecheck(e2)
        self.assert_same(e1, e2)

    def test_mapget_of_makemap(self):
        t = THandle("T", INT)
        xs = EVar("xs").with_type(TBag(t))
        x = EVar("x").with_type(t)
        y = EVar("y").with_type(t)
        mt = TTuple((INT, INT))
        e1 = EMapGet(
            EMakeMap2(xs, ELambda(x,
                ETuple((EGetField(x, "val").with_type(INT), EGetField(y, "val").with_type(INT))).with_type(mt)
                )).with_type(TMap(t, mt)),
            y).with_type(mt)
        e2 = ECond(
            EIn(e1.key, e1.map.e),
            e1.map.value.apply_to(EUnaryOp(UOp.The, EFilter(e1.map.e, mk_lambda(e1.map.value.arg.type, lambda foo: EEq(foo, e1.key))).with_type(e1.map.e.type)).with_type(e1.map.e.type.t)),
            construct_value(e1.type)).with_type(e1.type)
        self.assert_same(e1, e2)

    def test_map_eq(self):
        k = TNative("V")
        v = TBag(THandle("H", k))
        t = TMap(k, v)
        m1 = EVar("m1").with_type(t)
        m2 = EVar("m1").with_type(t)

        e = EImplies(EEq(m1, m2), EEq(EMapKeys(m1), EMapKeys(m2)))
        assert retypecheck(e)
        assert valid(e, collection_depth=3)

        k = EVar("k").with_type(t.k)
        e = EImplies(EEq(m1, m2), EEq(EMapGet(m1, k), EMapGet(m2, k)))
        assert retypecheck(e)
        assert valid(e, collection_depth=3)

    def test_argmin(self):
        xs = EVar("xs").with_type(INT_BAG)
        ys = EVar("ys").with_type(INT_BAG)
        id = mk_lambda(INT, lambda x: x)
        e1 = EArgMin(EBinOp(xs, "+", ys), id)
        e2 = ECond(EUnaryOp(UOp.Empty, xs), EArgMin(ys, id),
             ECond(EUnaryOp(UOp.Empty, ys), EArgMin(xs, id),
                EArgMin(EBinOp(
                    ESingleton(EArgMin(xs, id)),
                    "+",
                    ESingleton(EArgMin(ys, id))), id)))
        assert retypecheck(e1)
        assert retypecheck(e2)
        self.assert_same(e1, e2)

    def test_haskey(self):
        m = EVar("m").with_type(TMap(INT, INT))
        k = EVar("k").with_type(INT)
        e1 = EHasKey(m, k).with_type(BOOL)
        e2 = EIn(k, EMapKeys(m).with_type(TSet(INT)))
        self.assert_same(e1, e2)

    def test_edeepin(self):
        ht = THandle("H", INT)
        hb = EVar("hb").with_type(TBag(ht))
        h = fresh_var(ht, omit=free_vars(hb))
        arg = fresh_var(ht, omit=free_vars(h)|free_vars(hb))
        f1 = EDeepIn(h, hb)
        f2 = EUnaryOp(UOp.Any, EMap(hb, ELambda(arg, EBinOp(arg, "===", h).with_type(BOOL))).with_type(BOOL_BAG)).with_type(BOOL)
        self.assert_same(f1, f2)
