import unittest

from cozy.syntax_tools import mk_lambda, pprint
from cozy.target_syntax import *
from cozy.typecheck import typecheck

class TestTypechecking(unittest.TestCase):

    def test_map_over_noncollection(self):
        x = EVar("x").with_type(TInt())
        e = EMap(x, mk_lambda(TInt(), lambda elem: EBool(True)))
        errs = typecheck(e, { x.id : x.type })
        assert errs

    def test_map_incorrect_key_type(self):
        x = EVar("x").with_type(TBag(TInt()))
        e = EMap(x, mk_lambda(TBool(), lambda elem: EBool(True)))
        errs = typecheck(e, { x.id : x.type })
        assert errs

    def test_filter_over_noncollection(self):
        x = EVar("x").with_type(TInt())
        e = EFilter(x, mk_lambda(TInt(), lambda elem: EBool(True)))
        errs = typecheck(e, { x.id : x.type })
        assert errs

    def test_filter_incorrect_key_type(self):
        x = EVar("x").with_type(TBag(TInt()))
        e = EFilter(x, mk_lambda(TBool(), lambda elem: EBool(True)))
        errs = typecheck(e, { x.id : x.type })
        assert errs
