import unittest

from cozy.synthesis.rep_inference import infer_rep
from cozy.syntax_tools import mk_lambda, pprint, free_vars
from cozy.target_syntax import *
from cozy.typecheck import typecheck

def check_wt(vars, input):
    env = { v.id:v.type for v in free_vars(input) }

    inp_errs = typecheck(input, env)
    assert not inp_errs

    for (st, e) in infer_rep(vars, input):
        errs = []
        for (_, proj) in st:
            errs += typecheck(proj, env)
        errs += typecheck(e, env={ v.id:v.type for v in list(free_vars(input)) + [u for (u, proj) in st] })
        if errs:
            print("rep inference did a bad thing!")
            print("input = {}".format(pprint(input)))
            for v, proj in st:
                print("    {} : {} = {}".format(v.id, v.type, proj))
            print("    return {} : {}".format(pprint(e), e.type))
            for err in errs:
                print(" --> {}".format(err))
            raise Exception()

        yield (st, e)

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
        check_wt([ys], e)
