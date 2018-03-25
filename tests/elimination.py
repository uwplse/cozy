import unittest

from cozy.common import OrderedSet
from cozy.target_syntax import *
from cozy.syntax_tools import *
from cozy.typecheck import retypecheck
from cozy.solver import valid
from cozy.evaluation import eval

def _cse(e):
    return cse_replace(e, *cse_scan(e))

class TestElimination(unittest.TestCase):
    def test_y_plus_1(self):
        y = EVar("y").with_type(INT)
        yp1 = EBinOp(y, "+", ENum(1).with_type(INT))

        e = EBinOp(
                yp1,
                "+",
                yp1
            )

        assert retypecheck(e)
        print(pprint(e))

        e3 = _cse(e)
        newForm = pprint(e3)
        print(newForm)

        assert newForm.count("y + 1") == 1

    def test_y_plus_1_elambda(self):
        """
        (
            (y + 1) + (z + 1)
            +
            (let y = 9 in ( (y + 1) + (z + 1) + (y + 1) ))
        ) +
        (z + 1)
        """
        y = EVar("y").with_type(INT)
        yp1 = EBinOp(y, "+", ENum(1).with_type(INT))

        z = EVar("z").with_type(INT)
        zp1 = EBinOp(z, "+", ENum(1).with_type(INT))

        NINE = ENum(9).with_type(INT)

        e = EBinOp(
                EBinOp(
                    EBinOp(yp1, "+", zp1),
                    "+",
                    ELet(NINE,
                        ELambda(
                            EVar("y").with_type(INT),
                            EBinOp(
                                EBinOp(yp1, "+", zp1),
                                "+",
                                yp1
                            )
                        )
                    )
                ),
                "+",
                zp1)

        assert retypecheck(e)
        print(pprint(e))

        e3 = _cse(e)
        newForm = pprint(e3)
        print(newForm)

        assert newForm.count("y + 1") == 2
        assert newForm.count("z + 1") == 1

    def test_y_plus_1_elambda_z_post(self):
        """
        (
            (y + 1)
            +
            (let y = 9 in ( (y + 1) + (z + 1) + (y + 1) ))
        ) +
        (z + 1)
        """
        y = EVar("y").with_type(INT)
        yp1 = EBinOp(y, "+", ENum(1).with_type(INT))

        z = EVar("z").with_type(INT)
        zp1 = EBinOp(z, "+", ENum(1).with_type(INT))

        NINE = ENum(9).with_type(INT)

        e = EBinOp(
                EBinOp(
                    yp1,
                    "+",
                    ELet(NINE,
                        ELambda(
                            EVar("y").with_type(INT),
                            EBinOp(
                                EBinOp(yp1, "+", zp1),
                                "+",
                                yp1
                            )
                        )
                    )
                ),
                "+",
                zp1)

        assert retypecheck(e)
        print(pprint(e))

        e3 = _cse(e)
        newForm = pprint(e3)
        print(newForm)

        assert newForm.count("z + 1") == 1

    def test_y_plus_1_3x(self):
        """
            (y + 1)
            +
            (z + 1)
        +
            (y + 1)
        """
        y = EVar("y").with_type(INT)
        yp1 = EBinOp(y, "+", ENum(1).with_type(INT))

        z = EVar("z").with_type(INT)
        zp1 = EBinOp(z, "+", ENum(1).with_type(INT))

        NINE = ENum(9).with_type(INT)

        e = EBinOp(
                EBinOp(
                    yp1,
                    "+",
                    zp1
                ),
                "+",
                yp1)

        assert retypecheck(e)
        print(pprint(e))

        e3 = _cse(e)
        newForm = pprint(e3)
        print(newForm)

        assert newForm.count("y + 1") == 1
        assert newForm.count("z + 1") == 1

    def test_cse_2_expr(self):
        """
        (x < y)
            ? ((x < y) ? x + y : x + y)
            : ((x < y) ? x + y : x + y)
        """
        e = ECond(
                EBinOp(EVar("x").with_type(INT), "<", EVar("y").with_type(INT)),
                EBinOp(EVar("x").with_type(INT), "+", EVar("y").with_type(INT)),
                EBinOp(EVar("x").with_type(INT), "+", EVar("y").with_type(INT))
        )

        assert retypecheck(e)

        # Nested ECond:
        e2 = ECond(
                EBinOp(EVar("x").with_type(INT), "<", EVar("y").with_type(INT)),
                e,
                e
        )

        assert retypecheck(e2)
        print(pprint(e2))

        # Well, we have to do this 2x to achieve this one.
        e2 = _cse(e2)
        assert retypecheck(e2)
        e2 = _cse(e2)
        print(pprint(e2))
        print(e2)

        newForm = pprint(e2)
        assert newForm.count("x < y") == 1
        assert newForm.count("x + y") == 1

    def test_cse_2_exp_letscope(self):
        """
        (y + 2)
        +
        (let y = 1 in (y + 2))
        +
        (y + 2)

        The expression in the let should not be CSE'd. The outer ones should.
        """

        y = EVar("y").with_type(INT)
        yp2 = EBinOp(y, "+", ENum(2).with_type(INT))

        s = EBinOp(
                EBinOp(
                    yp2,
                    "+",
                    ELet(ONE, ELambda(y, yp2))),
                "+",
                yp2
            )

        assert retypecheck(s)
        print(pprint(s))

        s = _cse(s)
        print(pprint(s))
        print(s)

        assert "let y = 1 in (y + 2)" in pprint(s)
        assert isinstance(s, ELet)

    def test_cse_2_nolambda(self):
        """
        Bunch of different expressions should not get their ELambdas separated from them.
        """

        e1 = EFilter(ESingleton(ONE), ELambda(EVar("x").with_type(INT), EBinOp(EVar("x"), ">", ENum(2).with_type(INT))))
        e = ECond(EBinOp(EVar("x").with_type(INT), "<", EVar("y").with_type(INT)), e1, e1)
        assert retypecheck(e)
        e = _cse(e)
        assert isinstance(e1.p, ELambda)

        e1 = ELet(EVar("y").with_type(INT), ELambda(EVar("x").with_type(INT), EBinOp(EVar("x"), "+", ENum(2).with_type(INT))))
        e = ECond(EBinOp(EVar("x").with_type(INT), "<", EVar("y").with_type(INT)), e1, e1)
        assert retypecheck(e)
        e = _cse(e)
        assert isinstance(e1.f, ELambda)

        for t in (EMap, EArgMax, EArgMin):
            e1 = t(ESingleton(ONE), ELambda(EVar("x").with_type(INT), EBinOp(EVar("x"), "+", ENum(2).with_type(INT))))
            e = ECond(EBinOp(EVar("x").with_type(INT), "<", EVar("y").with_type(INT)), e1, e1)
            assert retypecheck(e)
            e = _cse(e)
            assert isinstance(e1.f, ELambda)

    def test_cse_2_stm_simple(self):
        """
        x = y + 2
        z = y + 2

        =>

        tmp = y + 2
        x = tmp
        z = tmp
        """
        yp2 = EBinOp(EVar("y").with_type(INT), "+", ENum(2).with_type(INT))

        s = SSeq(
                SAssign(EVar("x").with_type(INT), yp2),
                SAssign(EVar("z").with_type(INT), yp2),
        )

        assert retypecheck(s)

        print(pprint(s))
        s2 = _cse(s)
        new_form = pprint(s2)
        print(new_form)

        assert new_form.count("y + 2") == 1
