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
