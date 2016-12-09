import unittest

from cozy import incrementalization as inc
from cozy.target_syntax import *

class TestDerivative(unittest.TestCase):

    def test_tuple_deriv(self):
        x = EVar("x")
        y = EVar("y")
        e = ETuple((x, y))
        delta = inc.AddNum(ENum(1))
        deriv, subgoals = inc.derivative(e, x, delta, [])
        assert not subgoals
        assert deriv == inc.TupleEntryUpdate(0, delta), "got {}".format(deriv)

class TestApplyDelta(unittest.TestCase):

    def test_tuple_update(self):
        x = EVar("x").with_type(TInt())
        y = EVar("y").with_type(TInt())
        e = ETuple((x, y)).with_type(TTuple((TInt(), TInt())))
        delta = inc.TupleEntryUpdate(0, inc.AddNum(ENum(1)))
        new_exp = inc.apply_delta(e, delta)
        assert new_exp.type == e.type
        assert new_exp == ETuple((EBinOp(x, "+", ENum(1)), y))

    def test_tuple_update_in_place(self):
        e = EVar("tuple").with_type(TTuple((TInt(), TInt())))
        delta = inc.TupleEntryUpdate(0, inc.AddNum(ENum(1)))
        change = inc.apply_delta_in_place(e, delta)
        assert change == SAssign(ETupleGet(e, 0), EBinOp(ETupleGet(e, 0), "+", ENum(1)))
