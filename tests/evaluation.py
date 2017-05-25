import unittest

from cozy.target_syntax import *
from cozy.syntax_tools import *
from cozy.evaluation import eval, Bag
from cozy.typecheck import retypecheck

zero = ENum(0).with_type(INT)
one  = ENum(1).with_type(INT)

class TestEvaluation(unittest.TestCase):

    def test_mk_map(self):
        e = EMakeMap(EBinOp(ESingleton(zero), "+", ESingleton(one)),
            mk_lambda(INT, lambda i: zero),
            mk_lambda(TBag(INT), lambda ii: EMakeMap(ii,
                mk_lambda(INT, lambda i: one),
                mk_lambda(TBag(INT), lambda ii: EUnaryOp(UOp.Sum, ii)))))
        assert retypecheck(e)
        m = eval(e, env={})
        assert m[0][1] == 1
        assert 1 not in m.keys()
        assert 0 not in m[0].keys()

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
        assert m == Bag([1, 1])
        assert binds == [(x, i) for i in numbers]

    def test_leq(self):
        e = ZERO
        for i in range(50):
            e = ECond(EBinOp(e, "<=", ONE), ONE, ZERO).with_type(INT)
        res = eval(e, env={})
        print(res)
