import unittest

from cozy.common import OrderedSet
from cozy.target_syntax import *
from cozy.syntax_tools import *
from cozy.typecheck import retypecheck
from cozy.solver import valid
from cozy.evaluation import eval

class TestElimination(unittest.TestCase):
    def test_exprmap(self):
        y = EVar("x").with_type(INT)
        yp1 = EBinOp(y, "+", ENum(1).with_type(INT))

        e = EBinOp(
                yp1,
                "+",
                yp1
            )

        assert retypecheck(e)
        print(pprint(e))

        e2 = eliminate_common_subexpressions_stm(e)
        exprMap = ExpressionMap()

        e2 = process_expr(e, exprMap)
        print(pprint(e2))
        print(exprMap.by_id)
        print(exprMap.dependents)


        assert False
