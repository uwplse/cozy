import unittest

from cozy import incrementalization as inc
from cozy.target_syntax import *
from cozy.syntax_tools import equal, implies, pprint, mk_lambda
from cozy.solver import valid, satisfy
from cozy.typecheck import retypecheck
from cozy.evaluation import eval

def check_deriv(e, var, delta, expected, assumptions=()):
    print("applying delta {}".format(pprint(delta)))
    deriv, subgoals = inc.derivative(e, var, delta, [])
    print("derivative = {}".format(pprint(deriv)))
    applied = inc.apply_delta(e, deriv)
    print("applied = {}".format(pprint(applied)))
    cex = satisfy(ENot(implies(EAll(assumptions), equal(applied, expected))))
    assert cex is None, "expected = {}\ncex = {}\n|e| = {}\n|applied| = {}\n|expected| = {}".format(
        pprint(expected),
        repr(cex),
        eval(e, cex),
        eval(applied, cex),
        eval(expected, cex))

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

    def test_bag_elem_update(self):
        xs = EVar("xs").with_type(TBag(INT))
        e = EFilter(xs, mk_lambda(INT, lambda x: equal(x, ENum(0).with_type(INT))))
        assert retypecheck(e)
        delta = inc.BagElemUpdated(ENum(0).with_type(INT), inc.Become(ENum(1).with_type(INT)))
        expected = EEmptyList().with_type(e.type)
        check_deriv(e, xs, delta, expected)

    def test_bag_handle_elem_update(self):
        xs = EVar("xs").with_type(TBag(THandle("Elem", INT)))
        elem = EVar("x").with_type(xs.type.t)
        e = EFilter(xs, mk_lambda(elem.type, lambda x: equal(EGetField(x, "val"), ENum(0).with_type(INT))))
        assert retypecheck(e)
        delta = inc.BagElemUpdated(elem, inc.RecordFieldUpdate("val", inc.AddNum(ENum(1).with_type(INT))))
        expected = EFilter(xs, mk_lambda(elem.type, lambda x: equal(ECond(equal(x, elem), EBinOp(EGetField(x, "val"), "+", ENum(1).with_type(INT)), EGetField(x, "val")), ENum(0).with_type(INT))))
        assert retypecheck(expected)
        check_deriv(e, xs, delta, expected)

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
