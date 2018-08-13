from collections import OrderedDict
import unittest

from cozy.common import OrderedSet
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

    def test_complicated_adapt(self):
        e = EVar('p').with_type(TRecord((('partkey', TInt()), ('name', TString()), ('mfgr', TString()), ('brand', TString()), ('part_type', TString()), ('size', TInt()), ('container', TString()), ('retailprice', TFloat()), ('comment', TString()))))
        e_ctx = UnderBinder(parent=RootCtx(state_vars=OrderedSet([EVar('lineitem').with_type(TBag(TRecord((('orderkey', TInt()), ('partkey', TInt()), ('suppkey', TInt()), ('linenumber', TInt()), ('quantity', TFloat()), ('extendedprice', TFloat()), ('discount', TFloat()), ('tax', TFloat()), ('returnflag', TNative('char')), ('linestatus', TNative('char')), ('shipdate', TNative('uint64_t')), ('commitdate', TNative('uint64_t')), ('receiptdate', TNative('uint64_t')), ('shipinstruct', TString()), ('shipmode', TString()), ('comment', TString()))))), EVar('orders').with_type(TBag(TRecord((('orderkey', TInt()), ('custkey', TInt()), ('orderstatus', TNative('char')), ('totalprice', TFloat()), ('orderdate', TNative('uint64_t')), ('orderpriority', TString()), ('clerk', TString()), ('shippriority', TInt()), ('comment', TString()))))), EVar('part').with_type(TBag(TRecord((('partkey', TInt()), ('name', TString()), ('mfgr', TString()), ('brand', TString()), ('part_type', TString()), ('size', TInt()), ('container', TString()), ('retailprice', TFloat()), ('comment', TString()))))), EVar('customer').with_type(TBag(TRecord((('custkey', TInt()), ('name', TString()), ('address', TString()), ('nationkey', TInt()), ('phone', TString()), ('acctbal', TFloat()), ('mktsegment', TString()), ('comment', TString()))))), EVar('supplier').with_type(TBag(TRecord((('suppkey', TInt()), ('name', TString()), ('address', TString()), ('nationkey', TInt()), ('phone', TString()), ('acctbal', TFloat()), ('comment', TString()))))), EVar('partsupp').with_type(TBag(TRecord((('partkey', TInt()), ('suppkey', TInt()), ('availqty', TInt()), ('supplycost', TFloat()), ('comment', TString()))))), EVar('nation').with_type(TBag(TRecord((('nationkey', TInt()), ('name', TString()), ('regionkey', TInt()), ('comment', TString()))))), EVar('region').with_type(TBag(TRecord((('regionkey', TInt()), ('name', TString()), ('comment', TString())))))]), args=OrderedSet([EVar('orderkey').with_type(TInt()), EVar('partkey').with_type(TInt()), EVar('suppkey').with_type(TInt()), EVar('linenumber').with_type(TInt()), EVar('quantity').with_type(TFloat()), EVar('extendedprice').with_type(TFloat()), EVar('discount').with_type(TFloat()), EVar('tax').with_type(TFloat()), EVar('returnflag').with_type(TNative('char')), EVar('linestatus').with_type(TNative('char')), EVar('shipdate').with_type(TNative('uint64_t')), EVar('commitdate').with_type(TNative('uint64_t')), EVar('receiptdate').with_type(TNative('uint64_t')), EVar('shipinstruct').with_type(TString()), EVar('shipmode').with_type(TString()), EVar('comment').with_type(TString())]), funcs=OrderedDict([('div', TFunc((TFloat(), TFloat()), TFloat())), ('int2float', TFunc((TInt(),), TFloat())), ('brand23', TFunc((), TString())), ('medbox', TFunc((), TString()))])), v=EVar('p').with_type(TRecord((('partkey', TInt()), ('name', TString()), ('mfgr', TString()), ('brand', TString()), ('part_type', TString()), ('size', TInt()), ('container', TString()), ('retailprice', TFloat()), ('comment', TString())))), bag=EStateVar(EFilter(EFilter(EVar('part').with_type(TBag(TRecord((('partkey', TInt()), ('name', TString()), ('mfgr', TString()), ('brand', TString()), ('part_type', TString()), ('size', TInt()), ('container', TString()), ('retailprice', TFloat()), ('comment', TString()))))), ELambda(EVar('p').with_type(TRecord((('partkey', TInt()), ('name', TString()), ('mfgr', TString()), ('brand', TString()), ('part_type', TString()), ('size', TInt()), ('container', TString()), ('retailprice', TFloat()), ('comment', TString())))), EBinOp(EGetField(EVar('p').with_type(TRecord((('partkey', TInt()), ('name', TString()), ('mfgr', TString()), ('brand', TString()), ('part_type', TString()), ('size', TInt()), ('container', TString()), ('retailprice', TFloat()), ('comment', TString())))), 'brand').with_type(TString()), '==', ECall('brand23', ()).with_type(TString())).with_type(TBool()))).with_type(TBag(TRecord((('partkey', TInt()), ('name', TString()), ('mfgr', TString()), ('brand', TString()), ('part_type', TString()), ('size', TInt()), ('container', TString()), ('retailprice', TFloat()), ('comment', TString()))))), ELambda(EVar('p').with_type(TRecord((('partkey', TInt()), ('name', TString()), ('mfgr', TString()), ('brand', TString()), ('part_type', TString()), ('size', TInt()), ('container', TString()), ('retailprice', TFloat()), ('comment', TString())))), EBinOp(EGetField(EVar('p').with_type(TRecord((('partkey', TInt()), ('name', TString()), ('mfgr', TString()), ('brand', TString()), ('part_type', TString()), ('size', TInt()), ('container', TString()), ('retailprice', TFloat()), ('comment', TString())))), 'container').with_type(TString()), '==', ECall('medbox', ()).with_type(TString())).with_type(TBool()))).with_type(TBag(TRecord((('partkey', TInt()), ('name', TString()), ('mfgr', TString()), ('brand', TString()), ('part_type', TString()), ('size', TInt()), ('container', TString()), ('retailprice', TFloat()), ('comment', TString())))))).with_type(TBag(TRecord((('partkey', TInt()), ('name', TString()), ('mfgr', TString()), ('brand', TString()), ('part_type', TString()), ('size', TInt()), ('container', TString()), ('retailprice', TFloat()), ('comment', TString()))))), bag_pool=RUNTIME_POOL)
        dest_ctx = UnderBinder(parent=UnderBinder(parent=RootCtx(state_vars=OrderedSet([EVar('lineitem').with_type(TBag(TRecord((('orderkey', TInt()), ('partkey', TInt()), ('suppkey', TInt()), ('linenumber', TInt()), ('quantity', TFloat()), ('extendedprice', TFloat()), ('discount', TFloat()), ('tax', TFloat()), ('returnflag', TNative('char')), ('linestatus', TNative('char')), ('shipdate', TNative('uint64_t')), ('commitdate', TNative('uint64_t')), ('receiptdate', TNative('uint64_t')), ('shipinstruct', TString()), ('shipmode', TString()), ('comment', TString()))))), EVar('orders').with_type(TBag(TRecord((('orderkey', TInt()), ('custkey', TInt()), ('orderstatus', TNative('char')), ('totalprice', TFloat()), ('orderdate', TNative('uint64_t')), ('orderpriority', TString()), ('clerk', TString()), ('shippriority', TInt()), ('comment', TString()))))), EVar('part').with_type(TBag(TRecord((('partkey', TInt()), ('name', TString()), ('mfgr', TString()), ('brand', TString()), ('part_type', TString()), ('size', TInt()), ('container', TString()), ('retailprice', TFloat()), ('comment', TString()))))), EVar('customer').with_type(TBag(TRecord((('custkey', TInt()), ('name', TString()), ('address', TString()), ('nationkey', TInt()), ('phone', TString()), ('acctbal', TFloat()), ('mktsegment', TString()), ('comment', TString()))))), EVar('supplier').with_type(TBag(TRecord((('suppkey', TInt()), ('name', TString()), ('address', TString()), ('nationkey', TInt()), ('phone', TString()), ('acctbal', TFloat()), ('comment', TString()))))), EVar('partsupp').with_type(TBag(TRecord((('partkey', TInt()), ('suppkey', TInt()), ('availqty', TInt()), ('supplycost', TFloat()), ('comment', TString()))))), EVar('nation').with_type(TBag(TRecord((('nationkey', TInt()), ('name', TString()), ('regionkey', TInt()), ('comment', TString()))))), EVar('region').with_type(TBag(TRecord((('regionkey', TInt()), ('name', TString()), ('comment', TString())))))]), args=OrderedSet([EVar('orderkey').with_type(TInt()), EVar('partkey').with_type(TInt()), EVar('suppkey').with_type(TInt()), EVar('linenumber').with_type(TInt()), EVar('quantity').with_type(TFloat()), EVar('extendedprice').with_type(TFloat()), EVar('discount').with_type(TFloat()), EVar('tax').with_type(TFloat()), EVar('returnflag').with_type(TNative('char')), EVar('linestatus').with_type(TNative('char')), EVar('shipdate').with_type(TNative('uint64_t')), EVar('commitdate').with_type(TNative('uint64_t')), EVar('receiptdate').with_type(TNative('uint64_t')), EVar('shipinstruct').with_type(TString()), EVar('shipmode').with_type(TString()), EVar('comment').with_type(TString())]), funcs=OrderedDict([('div', TFunc((TFloat(), TFloat()), TFloat())), ('int2float', TFunc((TInt(),), TFloat())), ('brand23', TFunc((), TString())), ('medbox', TFunc((), TString()))])), v=EVar('l').with_type(TRecord((('orderkey', TInt()), ('partkey', TInt()), ('suppkey', TInt()), ('linenumber', TInt()), ('quantity', TFloat()), ('extendedprice', TFloat()), ('discount', TFloat()), ('tax', TFloat()), ('returnflag', TNative('char')), ('linestatus', TNative('char')), ('shipdate', TNative('uint64_t')), ('commitdate', TNative('uint64_t')), ('receiptdate', TNative('uint64_t')), ('shipinstruct', TString()), ('shipmode', TString()), ('comment', TString())))), bag=EBinOp(EStateVar(EVar('lineitem').with_type(TBag(TRecord((('orderkey', TInt()), ('partkey', TInt()), ('suppkey', TInt()), ('linenumber', TInt()), ('quantity', TFloat()), ('extendedprice', TFloat()), ('discount', TFloat()), ('tax', TFloat()), ('returnflag', TNative('char')), ('linestatus', TNative('char')), ('shipdate', TNative('uint64_t')), ('commitdate', TNative('uint64_t')), ('receiptdate', TNative('uint64_t')), ('shipinstruct', TString()), ('shipmode', TString()), ('comment', TString())))))).with_type(TBag(TRecord((('orderkey', TInt()), ('partkey', TInt()), ('suppkey', TInt()), ('linenumber', TInt()), ('quantity', TFloat()), ('extendedprice', TFloat()), ('discount', TFloat()), ('tax', TFloat()), ('returnflag', TNative('char')), ('linestatus', TNative('char')), ('shipdate', TNative('uint64_t')), ('commitdate', TNative('uint64_t')), ('receiptdate', TNative('uint64_t')), ('shipinstruct', TString()), ('shipmode', TString()), ('comment', TString()))))), '+', ESingleton(EMakeRecord((('orderkey', EVar('orderkey').with_type(TInt())), ('partkey', EVar('partkey').with_type(TInt())), ('suppkey', EVar('suppkey').with_type(TInt())), ('linenumber', EVar('linenumber').with_type(TInt())), ('quantity', EVar('quantity').with_type(TFloat())), ('extendedprice', EVar('extendedprice').with_type(TFloat())), ('discount', EVar('discount').with_type(TFloat())), ('tax', EVar('tax').with_type(TFloat())), ('returnflag', EVar('returnflag').with_type(TNative('char'))), ('linestatus', EVar('linestatus').with_type(TNative('char'))), ('shipdate', EVar('shipdate').with_type(TNative('uint64_t'))), ('commitdate', EVar('commitdate').with_type(TNative('uint64_t'))), ('receiptdate', EVar('receiptdate').with_type(TNative('uint64_t'))), ('shipinstruct', EVar('shipinstruct').with_type(TString())), ('shipmode', EVar('shipmode').with_type(TString())), ('comment', EVar('comment').with_type(TString())))).with_type(TRecord((('orderkey', TInt()), ('partkey', TInt()), ('suppkey', TInt()), ('linenumber', TInt()), ('quantity', TFloat()), ('extendedprice', TFloat()), ('discount', TFloat()), ('tax', TFloat()), ('returnflag', TNative('char')), ('linestatus', TNative('char')), ('shipdate', TNative('uint64_t')), ('commitdate', TNative('uint64_t')), ('receiptdate', TNative('uint64_t')), ('shipinstruct', TString()), ('shipmode', TString()), ('comment', TString()))))).with_type(TBag(TRecord((('orderkey', TInt()), ('partkey', TInt()), ('suppkey', TInt()), ('linenumber', TInt()), ('quantity', TFloat()), ('extendedprice', TFloat()), ('discount', TFloat()), ('tax', TFloat()), ('returnflag', TNative('char')), ('linestatus', TNative('char')), ('shipdate', TNative('uint64_t')), ('commitdate', TNative('uint64_t')), ('receiptdate', TNative('uint64_t')), ('shipinstruct', TString()), ('shipmode', TString()), ('comment', TString())))))).with_type(TBag(TRecord((('orderkey', TInt()), ('partkey', TInt()), ('suppkey', TInt()), ('linenumber', TInt()), ('quantity', TFloat()), ('extendedprice', TFloat()), ('discount', TFloat()), ('tax', TFloat()), ('returnflag', TNative('char')), ('linestatus', TNative('char')), ('shipdate', TNative('uint64_t')), ('commitdate', TNative('uint64_t')), ('receiptdate', TNative('uint64_t')), ('shipinstruct', TString()), ('shipmode', TString()), ('comment', TString()))))), bag_pool=RUNTIME_POOL), v=EVar('p').with_type(TRecord((('partkey', TInt()), ('name', TString()), ('mfgr', TString()), ('brand', TString()), ('part_type', TString()), ('size', TInt()), ('container', TString()), ('retailprice', TFloat()), ('comment', TString())))), bag=EStateVar(EFilter(EFilter(EVar('part').with_type(TBag(TRecord((('partkey', TInt()), ('name', TString()), ('mfgr', TString()), ('brand', TString()), ('part_type', TString()), ('size', TInt()), ('container', TString()), ('retailprice', TFloat()), ('comment', TString()))))), ELambda(EVar('p').with_type(TRecord((('partkey', TInt()), ('name', TString()), ('mfgr', TString()), ('brand', TString()), ('part_type', TString()), ('size', TInt()), ('container', TString()), ('retailprice', TFloat()), ('comment', TString())))), EBinOp(EGetField(EVar('p').with_type(TRecord((('partkey', TInt()), ('name', TString()), ('mfgr', TString()), ('brand', TString()), ('part_type', TString()), ('size', TInt()), ('container', TString()), ('retailprice', TFloat()), ('comment', TString())))), 'brand').with_type(TString()), '==', ECall('brand23', ()).with_type(TString())).with_type(TBool()))).with_type(TBag(TRecord((('partkey', TInt()), ('name', TString()), ('mfgr', TString()), ('brand', TString()), ('part_type', TString()), ('size', TInt()), ('container', TString()), ('retailprice', TFloat()), ('comment', TString()))))), ELambda(EVar('p').with_type(TRecord((('partkey', TInt()), ('name', TString()), ('mfgr', TString()), ('brand', TString()), ('part_type', TString()), ('size', TInt()), ('container', TString()), ('retailprice', TFloat()), ('comment', TString())))), EBinOp(EGetField(EVar('p').with_type(TRecord((('partkey', TInt()), ('name', TString()), ('mfgr', TString()), ('brand', TString()), ('part_type', TString()), ('size', TInt()), ('container', TString()), ('retailprice', TFloat()), ('comment', TString())))), 'container').with_type(TString()), '==', ECall('medbox', ()).with_type(TString())).with_type(TBool()))).with_type(TBag(TRecord((('partkey', TInt()), ('name', TString()), ('mfgr', TString()), ('brand', TString()), ('part_type', TString()), ('size', TInt()), ('container', TString()), ('retailprice', TFloat()), ('comment', TString())))))).with_type(TBag(TRecord((('partkey', TInt()), ('name', TString()), ('mfgr', TString()), ('brand', TString()), ('part_type', TString()), ('size', TInt()), ('container', TString()), ('retailprice', TFloat()), ('comment', TString()))))), bag_pool=RUNTIME_POOL)
        print("adapting {}".format(pprint(e)))
        print("in {}".format(e_ctx))
        print("to {}".format(dest_ctx))
        e_prime = dest_ctx.adapt(e, e_ctx)
        print(" ---> {}".format(pprint(e_prime)))
