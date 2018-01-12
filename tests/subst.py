import unittest

from cozy.syntax_tools import subst, pprint, mk_lambda, equal
from cozy.target_syntax import *
from cozy.solver import valid
from cozy.typecheck import retypecheck

class TestSubst(unittest.TestCase):

    def test_no_argument_conflict_lambda(self):
        x = EVar("x").with_type(TInt())
        y = EVar("y").with_type(TInt())
        f = ELambda(x, EBinOp(y, "+", ENum(1).with_type(INT)))
        assert retypecheck(f)

        g = subst(f, { y.id : x })
        a = EVar("a").with_type(TInt())
        b = EVar("b").with_type(TInt())
        assert valid(equal(g.apply_to(a), g.apply_to(b)))
