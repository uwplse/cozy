import unittest

from cozy.target_syntax import *
from cozy.syntax_tools import *
from cozy.evaluation import eval, Bag
from cozy.typecheck import retypecheck

zero = ENum(0).with_type(INT)
one  = ENum(1).with_type(INT)

class TestEvaluation(unittest.TestCase):

    def test_let(self):
        x = EVar("x").with_type(INT)
        e = ELet(ZERO, ELambda(x, ELet(ONE, ELambda(x, EBinOp(x, "+", x)))))
        assert retypecheck(e)
        assert eval(e, env={}) == 2

    def test_bind_callback(self):
        xs = EVar("xs").with_type(TBag(INT))
        x = EVar("x").with_type(INT)
        e = EFilter(xs, ELambda(x, equal(x, ENum(1).with_type(INT))))
        assert retypecheck(e)
        numbers = [0, 1, 1, 2, 3, 4]
        binds = []
        m = eval(e,
            env={xs.id: Bag(numbers)},
            bind_callback=lambda arg, val: binds.append((arg, val)))
        assert m == Bag([1, 1]), "m={}".format(m)
        assert binds == [(x, i) for i in numbers], "binds={}".format(binds)

    def test_leq(self):
        e = ZERO
        for i in range(50):
            e = ECond(EBinOp(e, "<=", ONE), ONE, ZERO).with_type(INT)
        res = eval(e, env={})
        print(res)
