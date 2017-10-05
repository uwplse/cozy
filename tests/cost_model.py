import unittest

from cozy.cost_model import Cost, CompositeCostModel
from cozy.typecheck import INT, retypecheck
from cozy.target_syntax import *
from cozy.syntax_tools import equal, implies, pprint, fresh_var, mk_lambda, replace, subst
from cozy.solver import valid
from cozy.rep_inference import pprint_reps, infer_rep
from cozy.pools import RUNTIME_POOL

cm = CompositeCostModel()
def cost_of(e):
    return cm.cost(e, RUNTIME_POOL)

class TestCostModel(unittest.TestCase):

    def test_map_vs_filter(self):
        # e1 = Filter {(\_var11 : xs.Handle -> ((_var11).val == z))} ((xs + []))
        xs = EVar("xs").with_type(TBag(INT))
        x = EVar("x").with_type(INT)
        y = EVar("y").with_type(INT)
        z = EVar("z").with_type(INT)
        e1 = EFilter(EBinOp(xs, "+", EEmptyList().with_type(xs.type)),
            ELambda(x, equal(x, z)))
        e2 = EMapGet(
            EStateVar(EMakeMap2(xs,
                ELambda(x, EFilter(xs, ELambda(y, EEq(y, x)))))),
            z)
        assert retypecheck(e1)
        assert retypecheck(e2)
        assert valid(equal(e1, e2))

        c1 = cost_of(e1)
        c2 = cost_of(e2)
        print(c1.compare_to(c2))
        assert c1.always_worse_than(c2), "{} @ {} > {} @ {}".format(pprint(e1), c1, pprint(e2), c2)

    def test_map_vs_const_filter(self):
        # e1 = Filter {(\_var11 : xs.Handle -> ((_var11).val == z))} ((xs + []))
        xs = EVar("xs").with_type(TBag(INT))
        x = EVar("x").with_type(INT)
        y = EVar("y").with_type(INT)
        e1 = EFilter(xs, ELambda(x, equal(x, ZERO)))
        e2 = EMapGet(
            EMakeMap2(xs,
                ELambda(x, EFilter(xs, ELambda(y, EEq(y, x))))),
            ZERO)
        assert retypecheck(e1)
        assert retypecheck(e2)
        assert valid(equal(e1, e2))

        c1 = cost_of(e1)
        c2 = cost_of(e2)
        assert c1.always_better_than(c2), "{} @ {} > {} @ {}".format(pprint(e1), c1, pprint(e2), c2)

    def test_true_filter(self):
        x = EVar("x").with_type(INT)
        y = EVar("y").with_type(INT)
        e1 = ESingleton(x)
        e2 = EFilter(e1, ELambda(y, T))
        assert retypecheck(e1)
        assert retypecheck(e2)
        assert cost_of(e1).compare_to(cost_of(e2)) == Cost.BETTER
        assert cost_of(e2).compare_to(cost_of(e1)) == Cost.WORSE

    def test_map_true_filter(self):
        x = EVar("x").with_type(INT)
        y = EVar("y").with_type(INT)
        f = ELambda(y, ZERO)
        e1 = ESingleton(x)
        e2 = EFilter(e1, ELambda(y, T))
        e1 = EMap(e1, f)
        e2 = EMap(e2, f)
        assert retypecheck(e1)
        assert retypecheck(e2)
        assert cost_of(e1).compare_to(cost_of(e2)) == Cost.BETTER
        assert cost_of(e2).compare_to(cost_of(e1)) == Cost.WORSE

    def test_eq_true_filter(self):
        x = EVar("x").with_type(INT)
        y = EVar("y").with_type(INT)
        f = ELambda(y, ZERO)
        e1 = ESingleton(x)
        e2 = EFilter(e1, ELambda(y, T))
        e1 = EEq(e1, e1)
        e2 = EEq(e2, e2)
        assert retypecheck(e1)
        assert retypecheck(e2)
        assert cost_of(e1).compare_to(cost_of(e2)) == Cost.BETTER
        assert cost_of(e2).compare_to(cost_of(e1)) == Cost.WORSE

    def test_eq_true_filter_in_filter(self):
        x = EVar("x").with_type(INT)
        y = EVar("y").with_type(INT)
        f = ELambda(y, ZERO)
        e1 = ESingleton(x)
        e2 = EFilter(e1, ELambda(y, T))
        e1 = EEq(e1, e1)
        e2 = EEq(e2, e2)
        e1 = EFilter(ESingleton(x), ELambda(y, e1))
        e2 = EFilter(ESingleton(x), ELambda(y, e2))
        assert retypecheck(e1)
        assert retypecheck(e2)
        assert cost_of(e1).compare_to(cost_of(e2)) == Cost.BETTER
        assert cost_of(e2).compare_to(cost_of(e1)) == Cost.WORSE

    def test_basics(self):
        ys = EVar('ys').with_type(TBag(THandle('ys', TInt())))
        e = EBinOp(EUnaryOp('sum', EFlatMap(EBinOp(ys, '+', EEmptyList().with_type(TBag(THandle('ys', TInt())))).with_type(TBag(THandle('ys', TInt()))), ELambda(EVar('_var12').with_type(THandle('ys', TInt())), ESingleton(ENum(1).with_type(TInt())).with_type(TBag(TInt())))).with_type(TBag(TInt()))).with_type(TInt()), '==', ENum(0).with_type(TInt())).with_type(TBool())
        assert cost_of(e).always_worse_than(Cost.ZERO)

    def test_add_empty(self):
        ys = EVar('ys').with_type(TBag(THandle('ys', TInt())))
        e1 = ys
        e2 = EBinOp(ys, "+", EEmptyList().with_type(ys.type))
        assert retypecheck(e1)
        assert retypecheck(e2)

        from cozy.rep_inference import infer_rep
        for ex in [e1, e2]:
            print("="*50 + " " + pprint(ex))
            for (st, e) in infer_rep([ys], ex):
                for (v, p) in st:
                    print("  {} : {} = {}".format(v.id, pprint(v.type), pprint(p)))
                print("  return {} : {}".format(pprint(e), pprint(e.type)))

        print("_" * 80)
        assert cost_of(e1).always_better_than(cost_of(e2)), "{} vs {}".format(cost_of(e1), cost_of(e2))

    def test_sum_empty(self):
        e1 = ENum(0).with_type(TInt())
        e2 = EUnaryOp("sum", EEmptyList().with_type(TBag(TInt()))).with_type(TInt())
        assert cost_of(e1).always_better_than(cost_of(e2)), "{} vs {}".format(cost_of(e1), cost_of(e2))

    def test_identity_map(self):
        xs = EVar("xs").with_type(TBag(INT))
        e1 = xs
        e2 = EMap(xs, mk_lambda(INT, lambda x: x))
        assert retypecheck(e1)
        assert retypecheck(e2)
        assert valid(equal(e1, e2))
        cost1 = cost_of(e1)
        cost2 = cost_of(e2)
        assert cost1.always_better_than(cost2), "{} vs {}".format(cost1, cost2)

    def test_tuples(self):
        sv = EVar("sv").with_type(THandle("T", INT))
        x = EVar("x").with_type(sv.type)
        e = ETupleGet(ETuple((sv, x)), 1)
        assert retypecheck(e)
        assert cost_of(e).always_worse_than(cost_of(x)), "cost of {} = {}, cost of {} = {}".format(pprint(e), cost_of(e), pprint(x), cost_of(x))

    def test_pointless_filter(self):
        Enum = TEnum(("A", "B", "C"))
        A, B, C = [EEnumEntry(case).with_type(Enum) for case in Enum.cases]
        Type = THandle("T", TRecord((("st", Enum),)))
        entries = EVar("xs").with_type(TBag(Type))
        entry = ESingleton(EVar("q").with_type(Type))
        zero = ENum(0).with_type(INT)
        one = ENum(1).with_type(INT)
        zero_the_hard_way = EUnaryOp(UOp.Sum, EMap(EFilter(entries, mk_lambda(Type, lambda x: F)), mk_lambda(Type, lambda x: one)))
        x = EVar("x").with_type(Type)
        p1 = EBinOp(equal(EGetField(EGetField(x, "val"), "st"), A), BOp.Or, equal(EGetField(EGetField(x, "val"), "st"), B))
        p2 = EBinOp(equal(zero, zero_the_hard_way), BOp.And, p1)
        e1 = EFilter(entry, ELambda(x, p1))
        e2 = EFilter(entry, ELambda(x, p2))
        assert retypecheck(e1), pprint(e1)
        assert retypecheck(e2), pprint(e2)
        assert valid(equal(e1, e2))
        assert cost_of(p1).always_better_than(cost_of(p2)), "cost_of(p1) == {}; cost_of(p2) == {}".format(cost_of(p1), cost_of(p2))
        assert cost_of(e1).always_better_than(cost_of(e2)), "cost_of(e1) == {}; cost_of(e2) == {}".format(cost_of(e1), cost_of(e2))

    def test_flatmap(self):
        costmodel = CompositeCostModel()
        t = THandle("T", INT)
        x = EVar("x").with_type(t)
        y = EVar("y").with_type(t)
        z = EVar("z").with_type(t)
        filt = EFilter(ESingleton(x), mk_lambda(t, lambda _: EEq(y, z)))
        e1 = EMap(filt, mk_lambda(t, lambda v: EWithAlteredValue(v, ZERO)))
        e2 = EFlatMap(filt, mk_lambda(t, lambda w: subst(e1, {x.id:w})))
        assert retypecheck(e1)
        assert retypecheck(e2)
        cost1 = costmodel.cost(e1, RUNTIME_POOL)
        cost2 = costmodel.cost(e2, RUNTIME_POOL)
        if not (cost1.always_better_than(cost2)):
            print("cost( {} ) = {}".format(pprint(e1), cost1))
            print("cost( {} ) = {}".format(pprint(e2), cost2))
            assert False

    def test_filter_singleton(self):
        x = EVar("x").with_type(INT)
        xs = EVar("xs").with_type(TBag(INT))
        e1 = EMap(EFilter(ESingleton(x), ELambda(x, EEq(x, ZERO))), ELambda(x, ONE))
        e2 = EMap(EFilter(EStateVar(xs), ELambda(x, EEq(x, ZERO))), ELambda(x, ONE))
        assert retypecheck(e1)
        assert retypecheck(e2)
        cost1 = cost_of(e1)
        cost2 = cost_of(e2)
        print("cost( {} ) = {}".format(pprint(e1), cost1))
        print("cost( {} ) = {}".format(pprint(e2), cost2))
        assumptions = EIn(x, xs)

        for x1, x2 in (("cost1", "cost2"), ("cost2", "cost1")):
            for f in ("always_better_than", "always_worse_than", "sometimes_better_than", "sometimes_worse_than"):
                print("@> {}.{}({}) = {}\n".format(x1, f, x2, getattr(locals()[x1], f)(locals()[x2], assumptions)))

        for op in "==", "<", "<=", ">", ">=":
            print("-"*10)
            print("cost1 {} cost2 = {}".format(op, cost1.always(op, cost2, T)))
            print("-"*10)

        ordering1 = cost1.compare_to(cost2, assumptions=assumptions)
        ordering2 = cost2.compare_to(cost1, assumptions=assumptions)
        print("cost1.compare_to(cost2) = {}".format(ordering1))
        print("cost2.compare_to(cost1) = {}".format(ordering2))

        assert ordering1 == "better"
        assert ordering2 == "worse"

    def test_regression1(self):
        e1 = EFilter(EUnaryOp('distinct', EBinOp(EUnaryOp('distinct', EMap(ESingleton(EVar('e').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))))).with_type(TBag(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))))), ELambda(EVar('_var156899').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))), EGetField(EGetField(EVar('_var156899').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))), 'val').with_type(TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))), 'inUse').with_type(TBool()))).with_type(TBag(TBool()))).with_type(TBag(TBool())), '+', EMap(ESingleton(EVar('e').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))))).with_type(TBag(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))))), ELambda(EVar('_var156899').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))), ECond(EBinOp(EVar('_var156899').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))), '==', EVar('e').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))))).with_type(TBool()), EVar('inUse').with_type(TBool()), EGetField(EGetField(EVar('_var156899').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))), 'val').with_type(TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))), 'inUse').with_type(TBool())).with_type(TBool()))).with_type(TBag(TBool()))).with_type(TBag(TBool()))).with_type(TBag(TBool())), ELambda(EVar('_var156894').with_type(TBool()), EBinOp(EBinOp(EGetField(EGetField(EVar('e').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))), 'val').with_type(TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))), 'st').with_type(TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), '==', EEnumEntry('DiskAndMemory').with_type(TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid')))).with_type(TBool()), 'or', EBinOp(EGetField(EGetField(EVar('e').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))), 'val').with_type(TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))), 'st').with_type(TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), '==', EEnumEntry('MemoryOnly').with_type(TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid')))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TBool()))
        e2 = EFilter(EUnaryOp('distinct', EBinOp(EUnaryOp('distinct', EMap(EFilter(EVar('entries').with_type(TBag(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))))), ELambda(EVar('_var156899').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))), EBinOp(EBinOp(EGetField(EGetField(EVar('e').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))), 'val').with_type(TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))), 'st').with_type(TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), '==', EEnumEntry('DiskAndMemory').with_type(TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid')))).with_type(TBool()), 'or', EBinOp(EGetField(EGetField(EVar('e').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))), 'val').with_type(TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))), 'st').with_type(TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), '==', EEnumEntry('MemoryOnly').with_type(TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid')))).with_type(TBool())).with_type(TBool()))).with_type(TBag(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))))), ELambda(EVar('_var156899').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))), EGetField(EGetField(EVar('_var156899').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))), 'val').with_type(TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))), 'inUse').with_type(TBool()))).with_type(TBag(TBool()))).with_type(TBag(TBool())), '+', EMap(EFilter(EVar('entries').with_type(TBag(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))))), ELambda(EVar('_var156899').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))), EBinOp(EBinOp(EGetField(EGetField(EVar('e').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))), 'val').with_type(TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))), 'st').with_type(TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), '==', EEnumEntry('DiskAndMemory').with_type(TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid')))).with_type(TBool()), 'or', EBinOp(EGetField(EGetField(EVar('e').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))), 'val').with_type(TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))), 'st').with_type(TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), '==', EEnumEntry('MemoryOnly').with_type(TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid')))).with_type(TBool())).with_type(TBool()))).with_type(TBag(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))))), ELambda(EVar('_var156899').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))), ECond(EBinOp(EVar('_var156899').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))), '==', EVar('e').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))))).with_type(TBool()), EVar('inUse').with_type(TBool()), EGetField(EGetField(EVar('_var156899').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))), 'val').with_type(TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))), 'inUse').with_type(TBool())).with_type(TBool()))).with_type(TBag(TBool()))).with_type(TBag(TBool()))).with_type(TBag(TBool())), ELambda(EVar('_var156894').with_type(TBool()), EBinOp(EBinOp(EGetField(EGetField(EVar('e').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))), 'val').with_type(TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))), 'st').with_type(TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), '==', EEnumEntry('DiskAndMemory').with_type(TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid')))).with_type(TBool()), 'or', EBinOp(EGetField(EGetField(EVar('e').with_type(THandle('Entry', TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool()))))), 'val').with_type(TRecord((('key', TNative('uint64_t')), ('pixmap', TNative('QPixmap *')), ('indexData', TNative('QByteArray')), ('memSize', TInt()), ('diskSize', TInt()), ('st', TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), ('inUse', TBool())))), 'st').with_type(TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid'))), '==', EEnumEntry('MemoryOnly').with_type(TEnum(('Disk', 'Loading', 'DiskAndMemory', 'MemoryOnly', 'Saving', 'NetworkPending', 'IndexPending', 'Invalid')))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TBool()))

        c1 = cost_of(e1)
        print(pprint(e1))
        print(c1)
        print()

        c2 = cost_of(e2)
        print(pprint(e2))
        print(c2)
        print()

        assert c1.compare_to(c2) == Cost.BETTER
