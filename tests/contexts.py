import unittest

from cozy.syntax import *
from cozy.pools import RUNTIME_POOL
from cozy.contexts import RootCtx, UnderBinder, shred
from cozy.structures.heaps import TMinHeap, EMakeMinHeap

x = EVar("x").with_type(INT)
y = EVar("y").with_type(INT)
z = EVar("z").with_type(INT)
int_bag = EVar("xs").with_type(INT_BAG)

class TestContexts(unittest.TestCase):

    def test_generalization1(self):
        root = RootCtx(args=[x, int_bag], state_vars=[])
        ctx = UnderBinder(root, y, int_bag, RUNTIME_POOL)
        assert ctx.generalize({x}) is root

    def test_generalization2(self):
        root = RootCtx(args=[x, int_bag], state_vars=[])
        ctx1 = UnderBinder(root, y, int_bag, RUNTIME_POOL)
        ctx2 = UnderBinder(ctx1, z, int_bag, RUNTIME_POOL)
        gen = ctx2.generalize({z})
        assert gen is not ctx2
        assert gen == UnderBinder(root, z, int_bag, RUNTIME_POOL)

    def test_generalization3(self):
        root = RootCtx(args=[x, int_bag], state_vars=[])
        ctx1 = UnderBinder(root, y, int_bag, RUNTIME_POOL)
        ctx2 = UnderBinder(ctx1, z, ESingleton(y).with_type(TBag(y.type)), RUNTIME_POOL)
        gen = ctx2.generalize({z})
        assert gen is ctx2

    def test_shred_minheap(self):
        f = ELambda(x, x)
        e = EMakeMinHeap(EEmptyList().with_type(INT_BAG), f).with_type(TMinHeap(INT, f))
        ctx = RootCtx(args=(), state_vars=())
        list(shred(e, ctx))
