import unittest

from cozy.synthesis.rep_inference import infer_rep
from cozy.syntax_tools import mk_lambda, pprint, free_vars
from cozy.target_syntax import *
from cozy.typecheck import typecheck

class TestRepInference(unittest.TestCase):

    def test_the_filter_typing(self):
        x = EVar("x").with_type(TBag(TInt()))
        y = EVar("y").with_type(TInt())
        e = EUnaryOp("the", EFilter(x, mk_lambda(x.type.t, lambda elem: EBinOp(elem, "==", y).with_type(TBool()))).with_type(x.type)).with_type(TMaybe(x.type.t))
        for (vars, e2) in infer_rep([x], e):
            for (v, proj) in vars:
                errs = typecheck(proj, env={ "x": x.type })
                assert not errs, "whoops! type error: {}".format(errs)
            errs = typecheck(e2, env=dict([(v.id, proj.type) for (v, proj) in vars] + [(x.id, x.type), (y.id, y.type)]))
            assert not errs, "whoops! type error: {}\nstate: {}\nres: {}".format(errs, vars, e2)

    def test_the_map_typing(self):
        x = EVar("x").with_type(TBag(TInt()))
        y = EVar("y").with_type(TInt())
        e = EUnaryOp("the", EMap(x, mk_lambda(x.type.t, lambda elem: EBinOp(elem, "==", y).with_type(TBool()))).with_type(x.type)).with_type(TMaybe(x.type.t))
        for (vars, e2) in infer_rep([x], e):
            for (v, proj) in vars:
                errs = typecheck(proj, env={ "x": x.type })
                assert not errs, "whoops! type error: {}".format(errs)
            errs = typecheck(e2, env=dict([(v.id, proj.type) for (v, proj) in vars] + [(x.id, x.type), (y.id, y.type)]))
            assert not errs, "whoops! type error: {}\nstate: {}\nres: {}".format(errs, vars, e2)

    def test_binop_typechecking(self):
        ys = EVar('ys').with_type(TBag(THandle('ys', TInt())))
        e = EBinOp(EBool(True).with_type(TBool()), 'and', EBinOp(ENum(0).with_type(TInt()), 'in', EMap(ys, ELambda(EVar('y').with_type(THandle('ys', TInt())), EGetField(EVar('y').with_type(THandle('ys', TInt())), 'val').with_type(TInt()))).with_type(TBag(TInt()))).with_type(TBool())).with_type(TBool())
        infer_rep([ys], e, validate_types=True)
