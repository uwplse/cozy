import unittest

from cozy.syntax_tools import alpha_equivalent, mk_lambda
from cozy.target_syntax import *

class TestAlphaEquivalent(unittest.TestCase):

    def test_binders(self):
        v1 = EVar("foo")
        e1 = EMap(v1, mk_lambda(TInt(), lambda arg: v1))
        e2 = EMap(v1, mk_lambda(TInt(), lambda arg: v1))
        assert e1.key_function.arg.id != e2.key_function.arg.id
        assert alpha_equivalent(e1, e2)

    def test_free_vars_not_equivalent(self):
        x = EVar("_var3423")
        y = EVar("_var3422")
        assert not alpha_equivalent(x, y)

    def test_mixed_binders(self):
        x = EVar("x")
        y = EVar("y")
        e1 = ELambda(x, ELambda(y, x))
        e2 = ELambda(x, ELambda(x, x))
        assert not alpha_equivalent(e1, e2)

    def test_lambdas(self):
        employers = EVar("employers").with_type(TBag(TInt()))
        e1 = mk_lambda(employers.type.elem_type, lambda employer: EGetField(EGetField(employer, "val"), "employer_name"))
        e2 = mk_lambda(employers.type.elem_type, lambda employer: EGetField(EGetField(employer, "val"), "employer_name"))
        assert alpha_equivalent(e1, e2)

    def test_tuples(self):
        one = ENum(1)
        e = ETuple((one, one))
        assert alpha_equivalent(e, e)

    def test_tuple_nontuple(self):
        one = ENum(1)
        e = ETuple((one, one))
        assert not alpha_equivalent(e, one)

    def test_make_record_other(self):
        assert not alpha_equivalent(
            EMakeRecord((("x", ENum(0)), ("y", ETRUE))),
            ETRUE)
        assert not alpha_equivalent(
            ETRUE,
            EMakeRecord((("x", ENum(0)), ("y", ETRUE))))

    def test_make_record_yes(self):
        assert alpha_equivalent(
            EMakeRecord((("x", ENum(0)), ("y", ETRUE))),
            EMakeRecord((("x", ENum(0)), ("y", ETRUE))))

    def test_make_record_no(self):
        assert not alpha_equivalent(
            EMakeRecord((("x", ENum(0)), ("y", ETRUE))),
            EMakeRecord((("z", ENum(0)), ("y", ETRUE))))

    def test_make_record_order_dependent(self):
        assert not alpha_equivalent(
            EMakeRecord((("x", ENum(0)), ("y", ETRUE))),
            EMakeRecord((("y", ETRUE), ("x", ENum(0)))))
