import unittest

from cozy.target_syntax import *
from cozy.typecheck import retypecheck
from cozy.syntax_tools import pprint
from cozy.pools import RUNTIME_POOL, STATE_POOL
from cozy.contexts import RootCtx, UnderBinder, shred, replace
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

    def test_replace_numeric_literal(self):
        f = ELambda(x, x)
        e = ENum(1.0).with_type(FLOAT)
        needle = ENum(1.0).with_type(FLOAT)
        replacement = ENum(0.0).with_type(FLOAT)
        ctx = RootCtx(args=(), state_vars=())
        res = replace(
            e, ctx, RUNTIME_POOL,
            needle, ctx, RUNTIME_POOL,
            replacement)
        assert res == replacement
        assert res.type == FLOAT

    def test_replace_different_typed_numeric_literal(self):
        f = ELambda(x, x)
        e = ENum(1.0).with_type(FLOAT)
        needle = ENum(1).with_type(INT)
        replacement = ENum(0).with_type(INT)
        ctx = RootCtx(args=(), state_vars=())
        res = replace(
            e, ctx, RUNTIME_POOL,
            needle, ctx, RUNTIME_POOL,
            replacement)
        assert res == e
        assert res.type == FLOAT

    def test_estatevar_ctx(self):
        xs = EVar("xs").with_type(INT_BAG)
        x = EVar("x").with_type(INT)
        y = EVar("y").with_type(BOOL)
        e = EMap(xs, ELambda(x, EStateVar(y)))
        ctx = RootCtx(args=(xs,), state_vars=(y,))
        assert retypecheck(e)
        for ee, ctx, pool in shred(e, ctx):
            if ee == y:
                assert isinstance(ctx, RootCtx)

        e = replace(
            e, ctx, RUNTIME_POOL,
            y, ctx, STATE_POOL,
            ETRUE)

        assert e == EMap(xs, ELambda(x, EStateVar(ETRUE))), pprint(e)

    def test_pool_affects_alpha_equivalence(self):
        e = EMap(EEmptyList().with_type(INT_BAG), ELambda(x, ONE))
        root_ctx = RootCtx(args=(), state_vars=())
        assert retypecheck(e)

        c1 = []
        for ee, ctx, pool in shred(e, root_ctx, RUNTIME_POOL):
            if ee == ONE:
                c1.append(ctx)
        assert len(c1) == 1
        c1 = c1[0]

        c2 = []
        for ee, ctx, pool in shred(e, root_ctx, STATE_POOL):
            if ee == ONE:
                c2.append(ctx)
        assert len(c2) == 1
        c2 = c2[0]

        assert c1 != c2
        assert not c1.alpha_equivalent(c2)

    def test_let(self):
        e1 = ELet(ZERO, ELambda(x, x))
        root_ctx = RootCtx(args=(), state_vars=())
        assert retypecheck(e1)
        n = 0
        for ee, ctx, pool in shred(e1, root_ctx, RUNTIME_POOL):
            if ee == x:
                e2 = replace(
                    e1, root_ctx, RUNTIME_POOL,
                    x, ctx, pool,
                    ZERO)
                assert e2 == ELet(ZERO, ELambda(x, ZERO))
                n += 1
        assert n == 1
