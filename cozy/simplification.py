from cozy.target_syntax import *
from cozy.syntax_tools import BottomUpRewriter, alpha_equivalent, cse
from cozy.evaluation import construct_value
from cozy.solver import valid, satisfy

class _V(BottomUpRewriter):
    def __init__(self, debug=False):
        self.debug = debug
    def visit_EBinOp(self, e):
        if e.op == BOp.In:
            if isinstance(e.e2, EBinOp) and e.e2.op == "+":
                return self.visit(EAny([EIn(e.e1, e.e2.e1), EIn(e.e1, e.e2.e2)]))
            elif isinstance(e.e2, EUnaryOp) and e.e2.op == UOp.Distinct:
                return self.visit(EIn(e.e1, e.e2.e))
            elif isinstance(e.e2, EFilter):
                return self.visit(EAll([EIn(e.e1, e.e2.e), e.e2.p.apply_to(e.e1)]))
        elif e.op in ("==", "==="):
            e1 = self.visit(e.e1)
            e2 = self.visit(e.e2)
            if alpha_equivalent(e1, e2):
                return T
            if e.op == "==":
                while isinstance(e1, EWithAlteredValue): e1 = e1.handle
                while isinstance(e2, EWithAlteredValue): e2 = e2.handle
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
        if cond == T:
            return self.visit(e.then_branch)
        elif cond == F:
            return self.visit(e.else_branch)
        elif alpha_equivalent(self.visit(e.then_branch), self.visit(e.else_branch)):
            return self.visit(e.then_branch)
        return ECond(cond, self.visit(e.then_branch), self.visit(e.else_branch)).with_type(e.type)
    def visit_EWithAlteredValue(self, e):
        t = e.type
        addr = self.visit(e.handle)
        val = self.visit(e.new_value)
        while isinstance(addr, EWithAlteredValue): addr = addr.handle
        if isinstance(addr, ECond):
            return self.visit(ECond(addr.cond,
                EWithAlteredValue(addr.then_branch, val).with_type(t),
                EWithAlteredValue(addr.else_branch, val).with_type(t)).with_type(t))
        return EWithAlteredValue(addr, val).with_type(t)
    def visit_EGetField(self, e):
        record = self.visit(e.e)
        if isinstance(record, ECond):
            return self.visit(ECond(record.cond,
                EGetField(record.then_branch, e.f).with_type(e.type),
                EGetField(record.else_branch, e.f).with_type(e.type)).with_type(e.type))
        if isinstance(record, EWithAlteredValue) and e.f == "val":
            return record.new_value
        if isinstance(record, EMakeRecord):
            return dict(record.fields)[e.f]
        return EGetField(record, e.f).with_type(e.type)
    def visit(self, e):
        new = super().visit(e)
        if self.debug and isinstance(e, Exp) and not isinstance(e, ELambda):
            model = satisfy(ENot(EBinOp(e, "===", new).with_type(BOOL)))
            if model is not None:
                from cozy.syntax_tools import pprint
                from cozy.evaluation import eval
                raise Exception("bad simplification: {} ---> {} (under model {!r}, got {!r} and {!r})".format(pprint(e), pprint(new), model, eval(e, model), eval(new, model)))
        return new

def simplify(e, debug=False):
    visitor = _V(debug)
    orig = e
    e = visitor.visit(e)
    # e = cse(e)
    if not valid(EBinOp(orig, "===", e).with_type(BOOL)):
        import sys
        print("simplify did something stupid!\nto reproduce:\nsimplify({e!r}, debug=True)".format(e=orig), file=sys.stderr)
        return orig
    return e
