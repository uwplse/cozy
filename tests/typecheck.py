import unittest

from cozy.syntax_tools import mk_lambda, pprint
from cozy.target_syntax import *
from cozy.typecheck import typecheck, retypecheck

class TestTypechecking(unittest.TestCase):

    def test_map_over_noncollection(self):
        x = EVar("x").with_type(TInt())
        e = EMap(x, mk_lambda(TInt(), lambda elem: EBool(True)))
        errs = typecheck(e, { x.id : x.type })
        assert errs

    def test_map_incorrect_key_type(self):
        x = EVar("x").with_type(TBag(TInt()))
        e = EMap(x, mk_lambda(TBool(), lambda elem: EBool(True)))
        errs = typecheck(e, { x.id : x.type })
        assert errs

    def test_filter_over_noncollection(self):
        x = EVar("x").with_type(TInt())
        e = EFilter(x, mk_lambda(TInt(), lambda elem: EBool(True)))
        errs = typecheck(e, { x.id : x.type })
        assert errs

    def test_filter_incorrect_key_type(self):
        x = EVar("x").with_type(TBag(TInt()))
        e = EFilter(x, mk_lambda(TBool(), lambda elem: EBool(True)))
        errs = typecheck(e, { x.id : x.type })
        assert errs

    def test_flatmap(self):
        e = EBinOp(EFlatMap(EBinOp(EVar('ys').with_type(TBag(THandle('ys', TInt()))), '+', EEmptyList().with_type(TBag(THandle('ys', TInt())))).with_type(TBag(THandle('ys', TInt()))), ELambda(EVar('_var12').with_type(THandle('ys', TInt())), EUnaryOp('sum', ESingleton(ENum(1).with_type(TInt())).with_type(TBag(TInt()))).with_type(TInt()))).with_type(TBag(TInt())), '==', ENum(0).with_type(TInt())).with_type(TBool())
        assert not retypecheck(e)

    def test_sum(self):
        xs = EVar("xs").with_type(TBag(TBool()))
        e = EUnaryOp("sum", xs)
        assert not retypecheck(e)
