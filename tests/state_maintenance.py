import unittest

from cozy.target_syntax import *
from cozy.syntax_tools import free_vars, pprint
from cozy.solver import valid
import cozy.state_maintenance as inc

class TestStateMaintenance(unittest.TestCase):

    def test_regression1(self):
        """
        Generated subgoals MUST NOT declare unused arguments
        """

        lval = EVar('_var6864').with_type(TInt())
        old_val = EUnaryOp('sum', EMap(EVar('records').with_type(TBag(THandle('Record', TRecord((('var', TInt()), ('level', TInt()), ('reason', TNative('org.sat4j.specs.Constr')), ('posWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('negWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('undos', TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>'))))))), ELambda(EVar('_var129').with_type(THandle('Record', TRecord((('var', TInt()), ('level', TInt()), ('reason', TNative('org.sat4j.specs.Constr')), ('posWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('negWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('undos', TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>')))))), ENum(1).with_type(TInt()))).with_type(TBag(TInt()))).with_type(TInt())
        new_val = EUnaryOp('sum', EMap(EMap(EVar('records').with_type(TBag(THandle('Record', TRecord((('var', TInt()), ('level', TInt()), ('reason', TNative('org.sat4j.specs.Constr')), ('posWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('negWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('undos', TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>'))))))), ELambda(EVar('_var37').with_type(THandle('Record', TRecord((('var', TInt()), ('level', TInt()), ('reason', TNative('org.sat4j.specs.Constr')), ('posWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('negWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('undos', TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>')))))), ECond(EBinOp(EVar('_var37').with_type(THandle('Record', TRecord((('var', TInt()), ('level', TInt()), ('reason', TNative('org.sat4j.specs.Constr')), ('posWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('negWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('undos', TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>')))))), '==', EVar('rec').with_type(THandle('Record', TRecord((('var', TInt()), ('level', TInt()), ('reason', TNative('org.sat4j.specs.Constr')), ('posWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('negWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('undos', TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>'))))))).with_type(TBool()), EWithAlteredValue(EVar('_var37').with_type(THandle('Record', TRecord((('var', TInt()), ('level', TInt()), ('reason', TNative('org.sat4j.specs.Constr')), ('posWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('negWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('undos', TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>')))))), EMakeRecord((('var', EGetField(EGetField(EVar('_var37').with_type(THandle('Record', TRecord((('var', TInt()), ('level', TInt()), ('reason', TNative('org.sat4j.specs.Constr')), ('posWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('negWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('undos', TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>')))))), 'val').with_type(TRecord((('var', TInt()), ('level', TInt()), ('reason', TNative('org.sat4j.specs.Constr')), ('posWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('negWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('undos', TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>'))))), 'var').with_type(TInt())), ('level', EVar('level').with_type(TInt())), ('reason', EGetField(EGetField(EVar('_var37').with_type(THandle('Record', TRecord((('var', TInt()), ('level', TInt()), ('reason', TNative('org.sat4j.specs.Constr')), ('posWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('negWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('undos', TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>')))))), 'val').with_type(TRecord((('var', TInt()), ('level', TInt()), ('reason', TNative('org.sat4j.specs.Constr')), ('posWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('negWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('undos', TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>'))))), 'reason').with_type(TNative('org.sat4j.specs.Constr'))), ('posWatches', EGetField(EGetField(EVar('_var37').with_type(THandle('Record', TRecord((('var', TInt()), ('level', TInt()), ('reason', TNative('org.sat4j.specs.Constr')), ('posWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('negWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('undos', TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>')))))), 'val').with_type(TRecord((('var', TInt()), ('level', TInt()), ('reason', TNative('org.sat4j.specs.Constr')), ('posWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('negWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('undos', TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>'))))), 'posWatches').with_type(TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>'))), ('negWatches', EGetField(EGetField(EVar('_var37').with_type(THandle('Record', TRecord((('var', TInt()), ('level', TInt()), ('reason', TNative('org.sat4j.specs.Constr')), ('posWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('negWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('undos', TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>')))))), 'val').with_type(TRecord((('var', TInt()), ('level', TInt()), ('reason', TNative('org.sat4j.specs.Constr')), ('posWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('negWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('undos', TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>'))))), 'negWatches').with_type(TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>'))), ('undos', EGetField(EGetField(EVar('_var37').with_type(THandle('Record', TRecord((('var', TInt()), ('level', TInt()), ('reason', TNative('org.sat4j.specs.Constr')), ('posWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('negWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('undos', TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>')))))), 'val').with_type(TRecord((('var', TInt()), ('level', TInt()), ('reason', TNative('org.sat4j.specs.Constr')), ('posWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('negWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('undos', TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>'))))), 'undos').with_type(TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>'))))).with_type(TRecord((('var', TInt()), ('level', TInt()), ('reason', TNative('org.sat4j.specs.Constr')), ('posWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('negWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('undos', TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>')))))).with_type(THandle('Record', TRecord((('var', TInt()), ('level', TInt()), ('reason', TNative('org.sat4j.specs.Constr')), ('posWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('negWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('undos', TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>')))))), EVar('_var37').with_type(THandle('Record', TRecord((('var', TInt()), ('level', TInt()), ('reason', TNative('org.sat4j.specs.Constr')), ('posWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('negWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('undos', TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>'))))))).with_type(THandle('Record', TRecord((('var', TInt()), ('level', TInt()), ('reason', TNative('org.sat4j.specs.Constr')), ('posWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('negWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('undos', TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>')))))))).with_type(TBag(THandle('Record', TRecord((('var', TInt()), ('level', TInt()), ('reason', TNative('org.sat4j.specs.Constr')), ('posWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('negWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('undos', TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>'))))))), ELambda(EVar('_var129').with_type(THandle('Record', TRecord((('var', TInt()), ('level', TInt()), ('reason', TNative('org.sat4j.specs.Constr')), ('posWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('negWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('undos', TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>')))))), ENum(1).with_type(TInt()))).with_type(TBag(TInt()))).with_type(TInt())
        ctx = [EVar('records').with_type(TBag(THandle('Record', TRecord((('var', TInt()), ('level', TInt()), ('reason', TNative('org.sat4j.specs.Constr')), ('posWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('negWatches', TNative('org.sat4j.specs.IVec<org.sat4j.specs.Propagatable>')), ('undos', TNative('org.sat4j.specs.IVec<org.sat4j.minisat.core.Undoable>')))))))]

        (code, subgoals) = inc.sketch_update(lval, old_val, new_val, ctx)
        for g in subgoals:
            for (v, t) in g.args:
                v = EVar(v).with_type(t)
                if v not in free_vars(g.ret) and not any(v in free_vars(a) for a in g.assumptions):
                    print("arg {} is not used in query".format(v.id))
                    print(pprint(g))
                    assert False

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
