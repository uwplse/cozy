"""Code generation for extension types.

This module provides `rewrite_extensions`, an important procedure that must run
before code generation.
"""

from collections import OrderedDict

from cozy.syntax import Spec, Exp
from cozy.target_syntax import EStm
from cozy.syntax_tools import BottomUpRewriter, shallow_copy, fresh_var
from cozy.structures import extension_handler

class _Rewriter(BottomUpRewriter):

    def __init__(self, concretization_functions):
        super().__init__()
        self.concretization_functions = concretization_functions

    def visit_Type(self, ty):
        h = extension_handler(type(ty))
        if h is not None:
            return self.visit(h.rep_type(ty))
        return self.visit_ADT(ty)

    def visit_Exp(self, e):
        h = extension_handler(type(e))
        if h is not None:
            v = fresh_var(self.visit(e.type))
            new_stm = h.codegen(e, self.concretization_functions, out=v)
            return EStm(new_stm, v).with_type(v.type)
        e = self.visit_ADT(e)
        if hasattr(e, "type"):
            e = shallow_copy(e).with_type(self.visit(e.type))
        return e

    def visit_SCall(self, s):
        h = extension_handler(type(s.target.type))
        if h is not None:
            return self.visit(h.implement_stmt(s, self.concretization_functions))
        return self.visit_ADT(s)

def rewrite_extensions(spec : Spec, concretization_functions : {str:Exp}) -> (Spec, {str:Exp}):
    """Remove all uses of extension structures from the given data structure.

    Input:
      spec - a data structure implementation
      concretization_functions - the concretization functions for the
        implementation

    Output:
      A pair containing the rewritten implementation and the rewritten
      concretization functions.

    Extension types know how to generate efficient code using simpler
    structures.  This function eliminates uses of extension structures for their
    simpler counterparts.  Note that this function's output is sutiable for code
    generation, but not for solving or evaluating internally.  Extensions are
    expanded automatically by the solver and evaluator, so there is no need for
    an equivalent version of this function for them.
    """
    new_spec = _Rewriter(concretization_functions).visit(spec)
    new_cc = OrderedDict()
    for name, exp in concretization_functions.items():
        new_cc[name] = _Rewriter({}).visit(exp)
    return new_spec, new_cc
