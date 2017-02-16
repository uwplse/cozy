import unittest

from cozy.syntax_tools import enumerate_fragments, equal, implies, pprint
from cozy.typecheck import retypecheck
from cozy.target_syntax import *
from cozy.solver import valid

class TestSyntaxTools(unittest.TestCase):

    def test_enumerate_fragments_strange_binder_behavior(self):
        xs = EVar("xs").with_type(TBag(INT))
        x = EVar("x").with_type(INT)
        xs_eq_zero = EFilter(xs, ELambda(x, equal(x, ZERO)))
        e = EFilter(xs_eq_zero, ELambda(x,
            equal(
                EFilter(xs, ELambda(x, T)),
                EEmptyList().with_type(xs.type))))
        assert retypecheck(e)
        for (a, e, r) in enumerate_fragments(e):
            if e == T:
                assert not valid(implies(EAll(a), equal(x, ZERO)), validate_model=True), "assumptions at {}: {}".format(pprint(e), "; ".join(pprint(aa) for aa in a))
