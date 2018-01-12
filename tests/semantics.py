import unittest

from cozy.target_syntax import *
from cozy.syntax_tools import mk_lambda, pprint
from cozy.typecheck import retypecheck
from cozy.solver import satisfy, valid
from cozy.distributivity import enumerate_forms
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

    # def test_regression1(self):
    #     for x in enumerate_forms(EMapGet(EMakeMap2(EMap(EBinOp(EStateVar(EVar('xs').with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), '+', ESingleton(EVar('x').with_type(THandle('T', TNative('X')))).with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), ELambda(EVar('_var5503').with_type(THandle('T', TNative('X'))), EGetField(EVar('_var5503').with_type(THandle('T', TNative('X'))), 'val').with_type(TNative('X')))).with_type(TBag(TNative('X'))), ELambda(EVar('_var5500').with_type(TNative('X')), EBool(True).with_type(TBool()))).with_type(TMap(TNative('X'), TBool())), EVar('_var3936').with_type(TNative('X'))).with_type(TBool()), debug=True):
    #         pass

    def test_regression2(self):
        for x in enumerate_forms(EFilter(EUnaryOp('distinct', EBinOp(EMapKeys(EMakeMap2(EStateVar(EVar('xs').with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), ELambda(EVar('_var842529').with_type(THandle('T', TNative('X'))), EMapGet(EMakeMap2(EMap(EStateVar(EVar('xs').with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), ELambda(EVar('_var842529').with_type(THandle('T', TNative('X'))), EGetField(EVar('_var842529').with_type(THandle('T', TNative('X'))), 'val').with_type(TNative('X')))).with_type(TBag(TNative('X'))), ELambda(EVar('_var842526').with_type(TNative('X')), EUnaryOp('len', EFilter(EMap(EStateVar(EVar('xs').with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), ELambda(EVar('_var842529').with_type(THandle('T', TNative('X'))), EGetField(EVar('_var842529').with_type(THandle('T', TNative('X'))), 'val').with_type(TNative('X')))).with_type(TBag(TNative('X'))), ELambda(EVar('_var842527').with_type(TNative('X')), EBinOp(EVar('_var842526').with_type(TNative('X')), '==', EVar('_var842527').with_type(TNative('X'))).with_type(TBool()))).with_type(TBag(TNative('X')))).with_type(TInt()))).with_type(TMap(TNative('X'), TInt())), EGetField(EVar('_var842529').with_type(THandle('T', TNative('X'))), 'val').with_type(TNative('X'))).with_type(TInt()))).with_type(TMap(THandle('T', TNative('X')), TInt()))).with_type(TBag(THandle('T', TNative('X')))), '+', EMapKeys(EMakeMap2(EBinOp(EStateVar(EVar('xs').with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), '+', ESingleton(EVar('x').with_type(THandle('T', TNative('X')))).with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), ELambda(EVar('_var842529').with_type(THandle('T', TNative('X'))), EMapGet(EMakeMap2(EMap(EBinOp(EStateVar(EVar('xs').with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), '+', ESingleton(EVar('x').with_type(THandle('T', TNative('X')))).with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), ELambda(EVar('_var842529').with_type(THandle('T', TNative('X'))), EGetField(EVar('_var842529').with_type(THandle('T', TNative('X'))), 'val').with_type(TNative('X')))).with_type(TBag(TNative('X'))), ELambda(EVar('_var842526').with_type(TNative('X')), EUnaryOp('len', EFilter(EMap(EBinOp(EStateVar(EVar('xs').with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), '+', ESingleton(EVar('x').with_type(THandle('T', TNative('X')))).with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), ELambda(EVar('_var842529').with_type(THandle('T', TNative('X'))), EGetField(EVar('_var842529').with_type(THandle('T', TNative('X'))), 'val').with_type(TNative('X')))).with_type(TBag(TNative('X'))), ELambda(EVar('_var842527').with_type(TNative('X')), EBinOp(EVar('_var842526').with_type(TNative('X')), '==', EVar('_var842527').with_type(TNative('X'))).with_type(TBool()))).with_type(TBag(TNative('X')))).with_type(TInt()))).with_type(TMap(TNative('X'), TInt())), EGetField(EVar('_var842529').with_type(THandle('T', TNative('X'))), 'val').with_type(TNative('X'))).with_type(TInt()))).with_type(TMap(THandle('T', TNative('X')), TInt()))).with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), ELambda(EVar('_var842529').with_type(THandle('T', TNative('X'))), EUnaryOp('not', EBinOp(EMapGet(EMakeMap2(EStateVar(EVar('xs').with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), ELambda(EVar('_var842529').with_type(THandle('T', TNative('X'))), EMapGet(EMakeMap2(EMap(EStateVar(EVar('xs').with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), ELambda(EVar('_var842529').with_type(THandle('T', TNative('X'))), EGetField(EVar('_var842529').with_type(THandle('T', TNative('X'))), 'val').with_type(TNative('X')))).with_type(TBag(TNative('X'))), ELambda(EVar('_var842526').with_type(TNative('X')), EUnaryOp('len', EFilter(EMap(EStateVar(EVar('xs').with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), ELambda(EVar('_var842529').with_type(THandle('T', TNative('X'))), EGetField(EVar('_var842529').with_type(THandle('T', TNative('X'))), 'val').with_type(TNative('X')))).with_type(TBag(TNative('X'))), ELambda(EVar('_var842527').with_type(TNative('X')), EBinOp(EVar('_var842526').with_type(TNative('X')), '==', EVar('_var842527').with_type(TNative('X'))).with_type(TBool()))).with_type(TBag(TNative('X')))).with_type(TInt()))).with_type(TMap(TNative('X'), TInt())), EGetField(EVar('_var842529').with_type(THandle('T', TNative('X'))), 'val').with_type(TNative('X'))).with_type(TInt()))).with_type(TMap(THandle('T', TNative('X')), TInt())), EVar('_var842529').with_type(THandle('T', TNative('X')))).with_type(TInt()), '==', EMapGet(EMakeMap2(EBinOp(EStateVar(EVar('xs').with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), '+', ESingleton(EVar('x').with_type(THandle('T', TNative('X')))).with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), ELambda(EVar('_var842529').with_type(THandle('T', TNative('X'))), EMapGet(EMakeMap2(EMap(EBinOp(EStateVar(EVar('xs').with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), '+', ESingleton(EVar('x').with_type(THandle('T', TNative('X')))).with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), ELambda(EVar('_var842529').with_type(THandle('T', TNative('X'))), EGetField(EVar('_var842529').with_type(THandle('T', TNative('X'))), 'val').with_type(TNative('X')))).with_type(TBag(TNative('X'))), ELambda(EVar('_var842526').with_type(TNative('X')), EUnaryOp('len', EFilter(EMap(EBinOp(EStateVar(EVar('xs').with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), '+', ESingleton(EVar('x').with_type(THandle('T', TNative('X')))).with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), ELambda(EVar('_var842529').with_type(THandle('T', TNative('X'))), EGetField(EVar('_var842529').with_type(THandle('T', TNative('X'))), 'val').with_type(TNative('X')))).with_type(TBag(TNative('X'))), ELambda(EVar('_var842527').with_type(TNative('X')), EBinOp(EVar('_var842526').with_type(TNative('X')), '==', EVar('_var842527').with_type(TNative('X'))).with_type(TBool()))).with_type(TBag(TNative('X')))).with_type(TInt()))).with_type(TMap(TNative('X'), TInt())), EGetField(EVar('_var842529').with_type(THandle('T', TNative('X'))), 'val').with_type(TNative('X'))).with_type(TInt()))).with_type(TMap(THandle('T', TNative('X')), TInt())), EVar('_var842529').with_type(THandle('T', TNative('X')))).with_type(TInt())).with_type(TBool())).with_type(TBool()))).with_type(TBag(THandle('T', TNative('X')))), debug=True):
            pass

    # def test_regression3(self):
    #     for x in enumerate_forms(EMapGet(EMakeMap2(EBinOp(EStateVar(EVar('xs').with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), '+', ESingleton(EVar('x').with_type(THandle('T', TNative('X')))).with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), ELambda(EVar('_var889080').with_type(THandle('T', TNative('X'))), EUnaryOp('len', EFilter(EMap(EBinOp(EStateVar(EVar('xs').with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), '+', ESingleton(EVar('x').with_type(THandle('T', TNative('X')))).with_type(TBag(THandle('T', TNative('X'))))).with_type(TBag(THandle('T', TNative('X')))), ELambda(EVar('_var889080').with_type(THandle('T', TNative('X'))), EGetField(EVar('_var889080').with_type(THandle('T', TNative('X'))), 'val').with_type(TNative('X')))).with_type(TBag(TNative('X'))), ELambda(EVar('_var889075').with_type(TNative('X')), EBinOp(EVar('_var889075').with_type(TNative('X')), '==', EGetField(EVar('_var889080').with_type(THandle('T', TNative('X'))), 'val').with_type(TNative('X'))).with_type(TBool()))).with_type(TBag(TNative('X')))).with_type(TInt()))).with_type(TMap(THandle('T', TNative('X')), TInt())), EVar('_var851045').with_type(THandle('T', TNative('X')))).with_type(TInt()), debug=True):
    #         pass

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
