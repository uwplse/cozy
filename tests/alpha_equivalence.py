import unittest

from cozy.syntax_tools import alpha_equivalent, pprint, mk_lambda
from cozy.target_syntax import *

class TestAlphaEquivalent(unittest.TestCase):

    def test_allow_rename(self):
        x = EVar("x").with_type(TInt())
        y = EVar("y").with_type(TInt())
        for b in [True, False]:
            aeq = alpha_equivalent(x, y, allow_rename=lambda v1, v2: b)
            assert aeq == b, "{} is {n}alpha-equiv to {}".format(pprint(x), pprint(y), n="" if aeq else "not ")

    def test_binders(self):
        v1 = EVar("foo")
        e1 = EMap(v1, mk_lambda(TInt(), lambda arg: v1))
        e2 = EMap(v1, mk_lambda(TInt(), lambda arg: v1))
        assert e1.f.arg.id != e2.f.arg.id
        assert alpha_equivalent(e1, e2)

    def test_lambdas(self):
        employers = EVar("employers").with_type(TBag(TInt()))
        e1 = mk_lambda(employers.type.t, lambda employer: EGetField(EGetField(employer, "val"), "employer_name"))
        e2 = mk_lambda(employers.type.t, lambda employer: EGetField(EGetField(employer, "val"), "employer_name"))
        assert alpha_equivalent(e1, e2)

    def test_make_map(self):
        employers = EVar("employers").with_type(TBag(TInt()))
        e1 = EMakeMap(employers, mk_lambda(employers.type.t, lambda employer: EGetField(EGetField(employer, "val"), "employer_name")), mk_lambda(employers.type, lambda es: es))
        e2 = EMakeMap(employers, mk_lambda(employers.type.t, lambda employer: EGetField(EGetField(employer, "val"), "employer_name")), mk_lambda(employers.type, lambda es: es))
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
            EMakeRecord((("x", ENum(0)), ("y", T))),
            T)
        assert not alpha_equivalent(
            T,
            EMakeRecord((("x", ENum(0)), ("y", T))))

    def test_make_record_yes(self):
        assert alpha_equivalent(
            EMakeRecord((("x", ENum(0)), ("y", T))),
            EMakeRecord((("x", ENum(0)), ("y", T))))

    def test_make_record_no(self):
        assert not alpha_equivalent(
            EMakeRecord((("x", ENum(0)), ("y", T))),
            EMakeRecord((("z", ENum(0)), ("y", T))))

    def test_make_record_order_dependent(self):
        assert not alpha_equivalent(
            EMakeRecord((("x", ENum(0)), ("y", T))),
            EMakeRecord((("y", T), ("x", ENum(0)))))
