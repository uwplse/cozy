import unittest

from cozy.common import OrderedSet
from cozy.target_syntax import *
from cozy.syntax_tools import *
from cozy.typecheck import retypecheck
from cozy.solver import valid
from cozy.evaluation import eval

class TestSyntaxTools(unittest.TestCase):

    def test_eall(self):
        assert eval(EAll(()), {})
        for l in range(5):
            print(pprint(EAll([EVar("v{}".format(i)).with_type(BOOL) for i in range(l)])))

    def test_enumerate_fragments_strange_binder_behavior(self):
        xs = EVar("xs").with_type(TBag(INT))
        x = EVar("x").with_type(INT)
        xs_eq_zero = EFilter(xs, ELambda(x, equal(x, ZERO)))
        e = EFilter(xs_eq_zero, ELambda(x,
            equal(
                EFilter(xs, ELambda(x, T)),
                EEmptyList().with_type(xs.type))))
        assert retypecheck(e)
        for (a, e, r, bound) in enumerate_fragments(e):
            if e == T:
                assert not valid(implies(EAll(a), equal(x, ZERO)), validate_model=True), "assumptions at {}: {}".format(pprint(e), "; ".join(pprint(aa) for aa in a))

    def test_enumerate_fragments_bound(self):
        b = EVar("b").with_type(BOOL)
        e = ELet(ZERO, mk_lambda(INT, lambda x: b))
        assert retypecheck(e)
        for (a, x, r, bound) in enumerate_fragments(e):
            if x == b:
                assert bound == { e.f.arg }, "got {}".format(bound)
            elif x == ZERO:
                assert bound == set(), "got {}".format(bound)

    def test_enumerate_fragments_estatevar(self):
        b = EVar("b").with_type(BOOL)
        e = ELet(ZERO, mk_lambda(INT, lambda x: EStateVar(b)))
        assert retypecheck(e)
        for (a, e, r, bound) in enumerate_fragments(e):
            if e == b:
                assert not bound, "EStateVar should reset bound variables, but got {}".format(bound)

    def test_enumerate_fragments_regression_1(self):
        e = EFilter(ESingleton(EVar('e').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))))).with_type(TBag(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))))), ELambda(EVar('_var380').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))), EBinOp(EVar('e').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))), 'in', EStateVar(EVar('entries').with_type(TBag(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))))).with_type(TBag(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))))).with_type(TBool()))).with_type(TBag(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))))
        for _ in enumerate_fragments(e):
            pass

    def test_cse(self):
        x = EVar("x").with_type(INT)
        a = EBinOp(x, "+", ONE).with_type(INT)
        e = EBinOp(a, "+", a).with_type(INT)
        e = EBinOp(e, "+", ELet(ONE, ELambda(x, EBinOp(x, "+", x).with_type(INT))).with_type(INT)).with_type(INT)
        print(pprint(e))
        print(pprint(cse(e)))
        assert valid(EEq(e, cse(e)))

    def test_fvs_depth(self):
        e = ZERO
        for i in range(500):
            e = ECond(EBinOp(e, "<=", ONE), ONE, ZERO).with_type(INT)
        res = free_vars(e)

    def test_fvs(self):
        e = EBinOp(EMapGet(EStateVar(EMakeMap2(EVar('l').with_type(TBag(INT)), ELambda(EVar('_var111').with_type(INT), EBinOp(EVar('_var111').with_type(INT), 'in', EVar('l').with_type(TBag(INT))).with_type(BOOL))).with_type(TMap(INT, BOOL))).with_type(TMap(INT, BOOL)), EVar('n').with_type(INT)).with_type(BOOL), '==', EBinOp(EVar('_var111').with_type(INT), 'in', EVar('l').with_type(TBag(INT))).with_type(BOOL)).with_type(BOOL)
        print(pprint(e))
        print(free_vars(e))
        assert free_vars(e) == OrderedSet([EVar('l').with_type(TBag(INT)), EVar('n').with_type(INT), EVar('_var111').with_type(INT)])

    def test_recursive_adt_repr(self):
        e = EStateVar(None)
        e.e = e
        print(repr(e))
        assert repr(e) == "EStateVar(<<recursive>>)"
