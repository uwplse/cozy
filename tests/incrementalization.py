import unittest

from cozy import incrementalization as inc
from cozy.target_syntax import *
from cozy.syntax_tools import equal, pprint
from cozy.solver import valid

class TestDerivative(unittest.TestCase):

    def test_tuple_deriv(self):
        x = EVar("x").with_type(INT)
        y = EVar("y").with_type(INT)
        tup = TTuple((INT, INT))
        e = ETuple((x, y)).with_type(tup)
        delta = inc.AddNum(ENum(1).with_type(INT))
        deriv, subgoals = inc.derivative(e, x, delta, [])
        print("derivative = {}".format(pprint(deriv)))
        assert not subgoals
        applied = inc.apply_delta(e, deriv)
        print("applied = {}".format(pprint(applied)))
        assert valid(equal(applied, ETuple((EBinOp(x, "+", ENum(1).with_type(INT)).with_type(INT), y)).with_type(tup)))

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
