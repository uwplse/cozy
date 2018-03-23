import unittest

from cozy.common import OrderedSet
from cozy.target_syntax import *
from cozy.syntax_tools import *
from cozy.typecheck import retypecheck
from cozy.solver import valid
from cozy.evaluation import eval

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

        exprMap = ExpressionMap()

        e2, deps = process_expr(e, exprMap)
        print(pprint(e2))

        e3 = cse_replace(e2, exprMap)
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

        exprMap = ExpressionMap()

        e2, deps = process_expr(e, exprMap)
        print(pprint(e2))

        e3 = cse_replace(e2, exprMap)
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

        exprMap = ExpressionMap()

        e2, deps = process_expr(e, exprMap)
        print(pprint(e2))

        e3 = cse_replace(e2, exprMap)
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

        exprMap = ExpressionMap()

        e2, deps = process_expr(e, exprMap)
        print(pprint(e2))

        e3 = cse_replace(e2, exprMap)
        newForm = pprint(e3)
        print(newForm)

        assert newForm.count("y + 1") == 1
        assert newForm.count("z + 1") == 1
