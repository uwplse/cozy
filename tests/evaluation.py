import unittest

from cozy.target_syntax import *
from cozy.syntax_tools import *
from cozy.evaluation import eval, Bag, Map, Handle, cmp, eq, EQ, LT, GT
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

    def test_map_eq(self):
        m = Map(TMap(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))), TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), 'Disk', [])
        assert m == m
        assert cmp(m.type, m, m) == EQ

    def test_deep_eq(self):
        t = THandle("H", INT)

        h1 = Handle(address=0, value=0)
        h2 = Handle(address=0, value=1)
        assert h1 != h2
        assert eq(t, h1, h2)

        h3 = Handle(address=1, value=0)
        b1 = Bag((h1, h3, h3))
        b2 = Bag((h3, h2, h3))
        assert b1 != b2
        assert eq(TBag(t), b1, b2)
