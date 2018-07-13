import unittest

from cozy.target_syntax import *
from cozy.desugar import desugar_list_comprehensions

class DesugaringTests(unittest.TestCase):

    def test_type_preservation(self):
        e1 = EListComprehension(EBinOp(ECall('log', (EBinOp(ENum(1.0).with_type(TFloat()), '+', EVar('x').with_type(TFloat())).with_type(TFloat()),)).with_type(TFloat()), '+', ECall('log', (ENum(1.5).with_type(TFloat()),)).with_type(TFloat())).with_type(TFloat()), (CPull('x', EListSlice(EVar('xs').with_type(TList(TFloat())), EVar('swapped').with_type(TInt()), EUnaryOp('len', EVar('xs').with_type(TList(TFloat()))).with_type(TInt())).with_type(TList(TFloat()))),)).with_type(TList(TFloat()))
        e2 = desugar_list_comprehensions(e1)
        assert e1.type == e2.type
