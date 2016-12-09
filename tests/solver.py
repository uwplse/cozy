import unittest

from cozy.solver import satisfy
from cozy.target_syntax import *

zero = ENum(0).with_type(TInt())
one  = ENum(1).with_type(TInt())

class TestSolver(unittest.TestCase):

    def test_the_empty(self):
        x = EEmptyList().with_type(TBag(TInt()))
        assert satisfy(EBinOp(EUnaryOp("the", x).with_type(TInt()), "==", EJust(one)).with_type(TBool())) is None
        assert satisfy(EBinOp(EUnaryOp("the", x).with_type(TInt()), "==", EJust(zero)).with_type(TBool())) is None

    def test_the(self):
        x = ESingleton(zero).with_type(TBag(TInt()))
        assert satisfy(EBinOp(EUnaryOp("the", x).with_type(TInt()), "==", EJust(one)).with_type(TBool())) is None
        assert satisfy(EBinOp(EUnaryOp("the", x).with_type(TInt()), "==", EJust(zero)).with_type(TBool())) is not None

    def test_the_nondeterminism(self):
        x = EBinOp(ESingleton(zero).with_type(TBag(TInt())), "+", ESingleton(one).with_type(TBag(TInt()))).with_type(TBag(TInt()))
        assert satisfy(EBinOp(EUnaryOp("the", x).with_type(TInt()), "==", EJust(one)).with_type(TBool())) is not None
        assert satisfy(EBinOp(EUnaryOp("the", x).with_type(TInt()), "==", EJust(zero)).with_type(TBool())) is not None
