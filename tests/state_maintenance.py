import unittest

from cozy.target_syntax import *
from cozy.structures.heaps import *
from cozy.typecheck import retypecheck
from cozy.syntax_tools import pprint, strip_EStateVar
from cozy.solver import valid
import cozy.state_maintenance as inc
from cozy.wf import repair_well_formedness
from cozy.contexts import RootCtx

class TestStateMaintenance(unittest.TestCase):

    def test_mutate_sequence_order1(self):

        e = EVar("xs").with_type(INT_BAG)
        x = EVar("x").with_type(INT)
        y = EVar("y").with_type(INT)
        s = SSeq(
            SCall(e, "add", (x,)),
            SCall(e, "remove", (y,)))

        assert valid(EDeepEq(
            inc.mutate(e, s),
            EBinOp(EBinOp(e, "+", ESingleton(x).with_type(INT_BAG)).with_type(INT_BAG), "-", ESingleton(y).with_type(INT_BAG)).with_type(INT_BAG)))

    def test_mutate_sequence_order2(self):

        e = EVar("xs").with_type(INT_BAG)
        x = EVar("x").with_type(INT)
        y = EVar("y").with_type(INT)
        s = SSeq(
            SCall(e, "remove", (y,)),
            SCall(e, "add", (x,)))

        assert valid(EDeepEq(
            inc.mutate(e, s),
            EBinOp(EBinOp(e, "-", ESingleton(y).with_type(INT_BAG)).with_type(INT_BAG), "+", ESingleton(x).with_type(INT_BAG)).with_type(INT_BAG)))

    def test_conditional(self):
        x = EVar("x").with_type(INT)
        b = EVar("b").with_type(BOOL)
        s = SIf(b, SAssign(x, ONE), SAssign(x, ZERO))
        assert valid(EEq(
            inc.mutate(x, s),
            ECond(b, ONE, ZERO).with_type(INT)))

    def test_heaps(self):
        sgs = []
        s = inc.mutate_in_place(
            lval=EVar('_var6975').with_type(TMinHeap(THandle('T', TNative('int')), TNative('int'))),
            e=EMakeMinHeap(EVar('xs').with_type(TBag(THandle('T', TNative('int')))), ELambda(EVar('_var2813').with_type(THandle('T', TNative('int'))), EGetField(EVar('_var2813').with_type(THandle('T', TNative('int'))), 'val').with_type(TNative('int')))).with_type(TMinHeap(THandle('T', TNative('int')), TNative('int'))),
            op=SCall(EVar('xs').with_type(TBag(THandle('T', TNative('int')))), 'remove', (EVar('x').with_type(THandle('T', TNative('int'))),)),
            abstract_state=[EVar('xs').with_type(TBag(THandle('T', TNative('int'))))],
            assumptions=[EBinOp(EVar('x').with_type(THandle('T', TNative('int'))), 'in', EVar('xs').with_type(TBag(THandle('T', TNative('int'))))).with_type(TBool()), EUnaryOp('all', EMap(EBinOp(EFlatMap(EVar('xs').with_type(TBag(THandle('T', TNative('int')))), ELambda(EVar('_var12').with_type(THandle('T', TNative('int'))), ESingleton(EVar('_var12').with_type(THandle('T', TNative('int')))).with_type(TBag(THandle('T', TNative('int')))))).with_type(TBag(THandle('T', TNative('int')))), '+', ESingleton(EVar('x').with_type(THandle('T', TNative('int')))).with_type(TBag(THandle('T', TNative('int'))))).with_type(TBag(THandle('T', TNative('int')))), ELambda(EVar('_var13').with_type(THandle('T', TNative('int'))), EUnaryOp('all', EMap(EBinOp(EFlatMap(EVar('xs').with_type(TBag(THandle('T', TNative('int')))), ELambda(EVar('_var12').with_type(THandle('T', TNative('int'))), ESingleton(EVar('_var12').with_type(THandle('T', TNative('int')))).with_type(TBag(THandle('T', TNative('int')))))).with_type(TBag(THandle('T', TNative('int')))), '+', ESingleton(EVar('x').with_type(THandle('T', TNative('int')))).with_type(TBag(THandle('T', TNative('int'))))).with_type(TBag(THandle('T', TNative('int')))), ELambda(EVar('_var14').with_type(THandle('T', TNative('int'))), EBinOp(EBinOp(EVar('_var13').with_type(THandle('T', TNative('int'))), '==', EVar('_var14').with_type(THandle('T', TNative('int')))).with_type(TBool()), '=>', EBinOp(EGetField(EVar('_var13').with_type(THandle('T', TNative('int'))), 'val').with_type(TNative('int')), '==', EGetField(EVar('_var14').with_type(THandle('T', TNative('int'))), 'val').with_type(TNative('int'))).with_type(TBool())).with_type(TBool()))).with_type(TBag(TBool()))).with_type(TBool()))).with_type(TBag(TBool()))).with_type(TBool())],
            subgoals_out=sgs)
        print("---")
        print(pprint(s))
        for g in sgs:
            print(pprint(g))
        print("---")

    def test_handle_writes(self):
        t = THandle("T", INT)
        x = EVar("x").with_type(t)
        y = EVar("y").with_type(t)
        z = EVar("z").with_type(t)
        e1 = EGetField(x, "val").with_type(t.value_type)
        e2 = inc.mutate(e1, SAssign(EGetField(y, "val").with_type(t.value_type), ZERO))
        assert not valid(EEq(e1, e2))
        assert valid(EImplies(ENot(EEq(x, y)), EEq(e1, e2)))

    def test_mutate_preserves_statevar(self):
        x = EVar("x").with_type(INT)
        e = EBinOp(EStateVar(x), "+", ONE)
        assert retypecheck(e)
        s = SAssign(x, EBinOp(x, "+", ONE).with_type(INT))
        e2 = strip_EStateVar(inc.mutate(e, s))
        e2 = repair_well_formedness(e2, context=RootCtx(state_vars=[x], args=[]))
        print(pprint(e))
        print(pprint(e2))
        assert e2 == EBinOp(EBinOp(EStateVar(x), "+", ONE), "+", ONE)
