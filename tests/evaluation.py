import unittest

from cozy.target_syntax import *
from cozy.syntax_tools import *
from cozy.value_types import Bag, Map, Handle, compare_values, values_equal, EQ
from cozy.structures.heaps import TMinHeap
from cozy.evaluation import eval, uneval
from cozy.typecheck import retypecheck

zero = ENum(0).with_type(INT)
one  = ENum(1).with_type(INT)

class TestEvaluation(unittest.TestCase):

    def test_bag_equality(self):
        b1 = Bag(((False, 10), (False, 12), (False, 6)))
        b2 = Bag(((False, 6), (False, 12), (False, 10)))
        assert b1 != b2

    def test_let(self):
        x = EVar("x").with_type(INT)
        e = ELet(ZERO, ELambda(x, ELet(ONE, ELambda(x, EBinOp(x, "+", x)))))
        assert retypecheck(e)
        assert eval(e, env={}) == 2

    def test_leq(self):
        e = ZERO
        for i in range(50):
            e = ECond(EBinOp(e, "<=", ONE), ONE, ZERO).with_type(INT)
        res = eval(e, env={})
        print(res)

    def test_map_eq(self):
        m = Map(TMap(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))), TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), 'Disk', [])
        assert m == m
        assert compare_values(m.type, m, m) == EQ

    def test_deep_eq(self):
        t = THandle("H", INT)

        h1 = Handle(address=0, value=0)
        h2 = Handle(address=0, value=1)
        assert h1 != h2
        assert values_equal(t, h1, h2)

        h3 = Handle(address=1, value=0)
        b1 = Bag((h1, h3, h3))
        b2 = Bag((h3, h2, h3))
        assert b1 != b2
        assert values_equal(TBag(t), b1, b2)

    def test_set_sub(self):
        t = TSet(INT)
        s1 = Bag((0, 1))
        s2 = Bag((1, 0))
        e = EEq(EBinOp(EVar("s1").with_type(t), "-", EVar("s2").with_type(t)), EEmptyList().with_type(t))
        assert retypecheck(e)
        assert eval(e, {"s1": s1, "s2": s2}) is True

    def test_heap_equality(self):
        t = TMinHeap(BOOL, INT)
        env = {
            "h1": Bag(((False, 7), (False, 13), (False, 13))),
            "h2": Bag(((False, 13), (False, 13), (False, 7))),
        }
        assert eval(EEq(EVar("h1").with_type(t), EVar("h2").with_type(t)), env)

    def test_bag_equality_with_tuple(self):
        assert (0, 1, 2) == Bag((0, 1, 2))
        assert Bag((0, 1, 2)) == (0, 1, 2)

    def test_makerecord(self):
        e = EMakeRecord((('orderkey', ENum(0).with_type(TInt())), ('custkey', ENum(0).with_type(TInt())), ('orderstatus', ENative(ENum(0).with_type(TInt())).with_type(TNative('char'))), ('totalprice', ENum(0).with_type(TFloat())), ('orderdate', ENative(ENum(0).with_type(TInt())).with_type(TNative('uint64_t'))), ('orderpriority', EStr('').with_type(TString())), ('clerk', EStr('').with_type(TString())), ('shippriority', ENum(0).with_type(TInt())), ('comment', EStr('').with_type(TString())))).with_type(TRecord((('orderkey', TInt()), ('custkey', TInt()), ('orderstatus', TNative('char')), ('totalprice', TFloat()), ('orderdate', TNative('uint64_t')), ('orderpriority', TString()), ('clerk', TString()), ('shippriority', TInt()), ('comment', TString()))))
        uneval(e.type, eval(e, {}))
