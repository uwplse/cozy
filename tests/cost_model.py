import unittest

from cozy.synthesis.high_level_interface import CoolCostModel
from cozy.target_syntax import *

class TestCostModel(unittest.TestCase):

    def test_basics(self):
        ys = EVar('ys').with_type(TBag(THandle('ys', TInt())))
        e = EBinOp(EUnaryOp('sum', EFlatMap(EBinOp(ys, '+', EEmptyList().with_type(TBag(THandle('ys', TInt())))).with_type(TBag(THandle('ys', TInt()))), ELambda(EVar('_var12').with_type(THandle('ys', TInt())), ESingleton(ENum(1).with_type(TInt())).with_type(TBag(TInt())))).with_type(TBag(TInt()))).with_type(TInt()), '==', ENum(0).with_type(TInt())).with_type(TBool())
        assert CoolCostModel([ys]).cost(e) > 0
