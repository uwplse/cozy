import unittest

from cozy.syntax_tools import mk_lambda
from cozy.target_syntax import *
from cozy.structures.heaps import *
from cozy.typecheck import typecheck, retypecheck

class TestTypechecking(unittest.TestCase):

    def test_map_over_noncollection(self):
        x = EVar("x").with_type(TInt())
        e = EMap(x, mk_lambda(TInt(), lambda elem: EBool(True)))
        errs = typecheck(e, { x.id : x.type })
        assert errs

    def test_filter_over_noncollection(self):
        x = EVar("x").with_type(TInt())
        e = EFilter(x, mk_lambda(TInt(), lambda elem: EBool(True)))
        errs = typecheck(e, { x.id : x.type })
        assert errs

    def test_flatmap(self):
        e = EBinOp(EFlatMap(EBinOp(EVar('ys').with_type(TBag(THandle('ys', TInt()))), '+', EEmptyList().with_type(TBag(THandle('ys', TInt())))).with_type(TBag(THandle('ys', TInt()))), ELambda(EVar('_var12').with_type(THandle('ys', TInt())), EUnaryOp('sum', ESingleton(ENum(1).with_type(TInt())).with_type(TBag(TInt()))).with_type(TInt()))).with_type(TBag(TInt())), '==', ENum(0).with_type(TInt())).with_type(TBool())
        assert not retypecheck(e)

    def test_sum(self):
        xs = EVar("xs").with_type(TBag(TBool()))
        e = EUnaryOp("sum", xs)
        assert not retypecheck(e)

    def test_ECond_1(self):
        x = ENum(1).with_type(INT)
        assert retypecheck(ECond(EBool(True), x, x))

    def test_ECond_2(self):
        x = ENum(1).with_type(INT)
        y = EBool(False)
        assert not retypecheck(ECond(EBool(True), x, y))

    def test_ECond_3(self):
        x = ENum(1).with_type(INT)
        y = EBool(False)
        assert not retypecheck(ECond(EBool(True), y, x))

    def test_ECond_4(self):
        x = ENum(1).with_type(INT)
        assert not retypecheck(ECond(x, x, x))

    def test_lambda_arg_inference(self):
        s = ESingleton(ETRUE)
        x = EVar("x")
        assert retypecheck(EFilter(s, ELambda(x, x)))
        assert retypecheck(EMap(s, ELambda(x, x)))
        assert retypecheck(EMakeMap2(s, ELambda(x, x)))

    def test_heaps(self):
        e = ECond(EBinOp(EBinOp(EMapGet(EStateVar(EMakeMap2(EVar('xs'), ELambda(EVar('_var39381'), EUnaryOp('len', EFilter(EVar('xs'), ELambda(EVar('_var39382'), EBinOp(EVar('_var39381'), '==', EVar('_var39382')))))))), ENum(0).with_type(INT)), '==', ENum(1).with_type(INT)), 'and', EBinOp(ENum(0).with_type(INT), '==', EStateVar(EArgMin(EVar('xs'), ELambda(EVar('_var21501'), EVar('_var21501')))))), EHeapPeek2(EStateVar(EMakeMinHeap(EVar('xs'), ELambda(EVar('_var21501'), EVar('_var21501')))), EStateVar(EUnaryOp('len', EVar('xs')))), EStateVar(EArgMin(EVar('xs'), ELambda(EVar('_var21501'), EVar('_var21501')))))
        assert retypecheck(e, env={
            "xs": INT_BAG,
            "_var21501": INT})
