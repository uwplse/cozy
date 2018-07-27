"""Helper methods to simplify expressions.

This is useful both to make expressions visually simpler for presentation and
to make them simpler for the synthesis backend.

The most important function is `simplify`.
"""

from cozy.target_syntax import *
from cozy.typecheck import is_collection, equality_implies_deep_equality
from cozy.syntax_tools import BottomUpRewriter, alpha_equivalent, compose, pprint, mk_lambda, replace
from cozy.evaluation import construct_value, eval
from cozy.solver import valid, satisfy
from cozy.opts import Option

checked_simplify = Option("checked-simplification", bool, False)

class _SimplificationVisitor(BottomUpRewriter):
    def __init__(self, debug=False):
        self.debug = debug
    def visit_EBinOp(self, e):
        if e.op == BOp.In:
            if isinstance(e.e2, EBinOp) and e.e2.op == "+":
                return self.visit(EAny([EIn(e.e1, e.e2.e1), EIn(e.e1, e.e2.e2)]))
            elif isinstance(e.e2, EUnaryOp) and e.e2.op == UOp.Distinct:
                return self.visit(EIn(e.e1, e.e2.e))
            elif isinstance(e.e2, EMapKeys):
                return self.visit(EHasKey(e.e2.e, e.e1).with_type(BOOL))
        elif e.op in ("==", "==="):
            e1 = self.visit(e.e1)
            e2 = self.visit(e.e2)
            if alpha_equivalent(e1, e2):
                return ETRUE
            if isinstance(e2, ECond) and alpha_equivalent(e1, e2.else_branch):
                return self.visit(EBinOp(ENot(e2.cond), BOp.Or, EBinOp(e1, e.op, e2.then_branch).with_type(BOOL)).with_type(BOOL))
            e = EBinOp(e1, e.op, e2).with_type(e.type)
        if isinstance(e.e1, ECond):
            return self.visit(ECond(e.e1.cond,
                EBinOp(e.e1.then_branch, e.op, e.e2).with_type(e.type),
                EBinOp(e.e1.else_branch, e.op, e.e2).with_type(e.type)).with_type(e.type))
        if isinstance(e.e2, ECond):
            return self.visit(ECond(e.e2.cond,
                EBinOp(e.e1, e.op, e.e2.then_branch).with_type(e.type),
                EBinOp(e.e1, e.op, e.e2.else_branch).with_type(e.type)).with_type(e.type))
        return EBinOp(self.visit(e.e1), e.op, self.visit(e.e2)).with_type(e.type)
    def visit_ECond(self, e):
        cond = self.visit(e.cond)
        if cond == ETRUE:
            return self.visit(e.then_branch)
        elif cond == EFALSE:
            return self.visit(e.else_branch)
        elif alpha_equivalent(self.visit(e.then_branch), self.visit(e.else_branch)):
            return self.visit(e.then_branch)
        tb = replace(e.then_branch, cond, ETRUE)
        eb = replace(e.else_branch, cond, EFALSE)
        return ECond(cond, self.visit(tb), self.visit(eb)).with_type(e.type)
    def visit_EGetField(self, e):
        record = self.visit(e.e)
        if isinstance(record, ECond):
            return self.visit(ECond(record.cond,
                EGetField(record.then_branch, e.field_name).with_type(e.type),
                EGetField(record.else_branch, e.field_name).with_type(e.type)).with_type(e.type))
        if isinstance(record, EMakeRecord):
            return dict(record.fields)[e.f]
        return EGetField(record, e.field_name).with_type(e.type)
    def visit_EFilter(self, e):
        ee = self.visit(e.e)
        f = self.visit(e.p)
        if f.body == ETRUE:
            return ee
        elif f.body == EFALSE:
            return EEmptyList().with_type(e.type)
        elif isinstance(ee, EBinOp) and ee.op == "+":
            return self.visit(EBinOp(EFilter(ee.e1, f).with_type(ee.e1.type), ee.op, EFilter(ee.e2, f).with_type(ee.e2.type)).with_type(e.type))
        elif isinstance(ee, ESingleton):
            return self.visit(ECond(
                f.apply_to(ee.e),
                ee,
                EEmptyList().with_type(e.type)).with_type(e.type))
        elif isinstance(ee, EMap):
            return self.visit(EMap(EFilter(ee.e, compose(f, ee.key_function)).with_type(ee.e.type), ee.key_function).with_type(e.type))
        return EFilter(ee, f).with_type(e.type)
    def visit_EMap(self, e):
        ee = self.visit(e.e)
        f = self.visit(e.key_function)
        if f.body == f.arg:
            return ee
        elif isinstance(ee, EBinOp) and ee.op == "+":
            return self.visit(EBinOp(EMap(ee.e1, f).with_type(e.type), ee.op, EMap(ee.e2, f).with_type(e.type)).with_type(e.type))
        elif isinstance(ee, ESingleton):
            return self.visit(ESingleton(f.apply_to(ee.e)).with_type(e.type))
        elif isinstance(ee, EMap):
            return self.visit(EMap(ee.e, compose(f, ee.key_function)).with_type(e.type))
        return EMap(ee, f).with_type(e.type)
    def visit_EMapKeys(self, e):
        ee = self.visit(e.e)
        if isinstance(ee, EMakeMap2):
            return self.visit(EUnaryOp(UOp.Distinct, ee.e).with_type(e.type))
        return EMapKeys(ee).with_type(e.type)
    def visit_EHasKey(self, e):
        ee = self.visit(e.map)
        if isinstance(ee, EMakeMap2):
            return self.visit(EIn(e.key, ee.e))
        return EHasKey(ee, self.visit(e.key)).with_type(BOOL)
    def visit_EMapGet(self, e):
        m = self.visit(e.map)
        k = self.visit(e.key)
        if isinstance(m, EMakeMap2):
            if equality_implies_deep_equality(k.type):
                return self.visit(ECond(
                    EIn(k, m.e),
                    m.value_function.apply_to(k),
                    construct_value(m.type.v)).with_type(m.type.v))
            else:
                return self.visit(EUnaryOp(UOp.The,
                        EMap(
                            EFilter(m.e,
                                mk_lambda(m.type.k, lambda kk: EEq(kk, k))).with_type(TBag(m.type.k)),
                            m.value_function).with_type(TBag(m.type.v))).with_type(m.type.v))
        return EMapGet(m, k).with_type(e.type)
    def visit_EUnaryOp(self, e):
        if isinstance(e.e, ECond):
            return self.visit(ECond(
                e.e.cond,
                EUnaryOp(e.op, e.e.then_branch).with_type(e.type),
                EUnaryOp(e.op, e.e.else_branch).with_type(e.type)).with_type(e.type))
        ee = self.visit(e.e)
        if e.op == UOp.Not:
            if isinstance(ee, EBool):
                return EFALSE if ee.val else ETRUE
        elif e.op in (UOp.Length, UOp.Sum):
            if isinstance(ee, EBinOp) and ee.op == "+":
                return self.visit(EBinOp(EUnaryOp(e.op, ee.e1).with_type(e.type), "+", EUnaryOp(e.op, ee.e2).with_type(e.type)).with_type(e.type))
            elif isinstance(ee, ESingleton):
                if e.op == UOp.Length:
                    return ENum(1).with_type(e.type)
                elif e.op == UOp.Sum:
                    return ee.e
            elif isinstance(ee, EEmptyList):
                return ENum(0).with_type(e.type)
            elif isinstance(ee, EMap) and e.op == UOp.Length:
                return self.visit(EUnaryOp(e.op, ee.e).with_type(e.type))
        elif e.op in (UOp.Exists, UOp.Empty):
            if isinstance(ee, EMap) or (isinstance(ee, EUnaryOp) and ee.op == UOp.Distinct):
                return self.visit(EUnaryOp(e.op, ee.e).with_type(e.type))
            elif isinstance(ee, EBinOp) and ee.op == "+":
                if e.op == UOp.Exists:
                    return self.visit(EAny([
                        EUnaryOp(e.op, ee.e1).with_type(BOOL),
                        EUnaryOp(e.op, ee.e2).with_type(BOOL)]))
                elif e.op == UOp.Empty:
                    return self.visit(EAll([
                        EUnaryOp(e.op, ee.e1).with_type(BOOL),
                        EUnaryOp(e.op, ee.e2).with_type(BOOL)]))
            elif isinstance(ee, EEmptyList):
                return ETRUE if e.op == UOp.Empty else EFALSE
            elif isinstance(ee, ESingleton):
                return ETRUE if e.op == UOp.Exists else EFALSE
        return EUnaryOp(e.op, ee).with_type(e.type)
    def visit(self, e):
        if hasattr(e, "_nosimpl"): return e
        if isinstance(e, Exp) and not isinstance(e, ELambda): t = e.type
        new = super().visit(e)
        if isinstance(e, Exp) and not isinstance(e, ELambda): assert new.type == e.type or (is_collection(new.type) and is_collection(e.type)), repr(e)
        if self.debug and isinstance(e, Exp) and not isinstance(e, ELambda):
            model = satisfy(ENot(EBinOp(e, "===", new).with_type(BOOL)))
            if model is not None:
                raise Exception("bad simplification: {} ---> {} (under model {!r}, got {!r} and {!r})".format(pprint(e), pprint(new), model, eval(e, model), eval(new, model)))
        return new

def simplify(e, validate=None, debug=False):
    if validate is None:
        validate = checked_simplify.value
    try:
        visitor = _SimplificationVisitor(debug)
        orig = e
        e = visitor.visit(e)
        # assert orig.type == e.type, "simplification changed the expression's type: {} --> {}".format(pprint(orig.type), pprint(e.type))
        # e = cse(e)
        if validate and not valid(EBinOp(orig, "===", e).with_type(BOOL)):
            import sys
            print("simplify did something stupid!\nto reproduce:\nsimplify({e!r}, validate=True, debug=True)".format(e=orig), file=sys.stderr)
            return orig
        return e
    except:
        print("SIMPL FAILED")
        print(repr(e))
        raise
