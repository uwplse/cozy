"""Simplification and optimization for Cozy-generated implementations.

The key methods are
 - stream
 - simplify_and_optimize
 - simplify_and_optimize_expression
"""

from cozy.syntax import (
    TSet, BOOL,
    Exp, EVar, ELambda, ELet, EListSlice, EEmptyList, ESingleton, ECond, EUnaryOp, UOp, EBinOp, BOp, ENot,
    Stm, SAssign, SIf, SForEach, SNoOp, seq, SSeq, SDecl, SCall)
from cozy.target_syntax import (
    EMap, EFilter, EFlatMap,
    EEmptyMap,
    SMapUpdate)
from cozy.syntax_tools import fresh_var, count_occurrences_of_free_var, subst, BottomUpRewriter
from cozy.typecheck import is_collection

from .misc import SScoped, SEscape, EMove

def stream(iterable : Exp, loop_var : EVar, body : Stm) -> Stm:
    """Convert an iterable expression to a streaming operation.

    Input:
      iterable - an expression with an iterable type (Bag, Set, or List), not
        yet optimized
      body - a function that accepts a loop variable and produces a statement
        to run on that variable, not yet optimized

    Output:
      A statement equivalent to
        for (loop_var in iterable) { body }
      that eliminates as many intermediate collections and objects as possible.

    NOTE: The output of function will not be correct if the body modifies any
    free variable in the iterable expression or writes to any pointers that
    are read by the iterable expression.

    Generating code for the expression

        Map {func} (Filter {predicate} big_collection)

    might create two new collections as large as `big_collection`: one to hold
    the result of the filter and one to hold the result of the map.  If all the
    code needs to do is to iterate over the result, then there is no reason to
    make the two new collections.

    This function is mutually recursive with `simplify_and_optimize`, so any
    transformations performed by that method are also applied to the output of
    this one.
    """

    if isinstance(iterable, EEmptyList):
        return SNoOp()
    elif isinstance(iterable, ESingleton):
        setup, value = simplify_and_optimize_expression(iterable.e)
        # SScoped because if the iterable is e.g. [x] + [y], then the body
        # might be appear in the same block twice.  If the body declares any
        # variables, that will cause problems in languages like Java or C++.
        return seq([setup, SScoped(re_use(value, loop_var, simplify_and_optimize(body)))])
    elif isinstance(iterable, ECond):
        # todo: optimize cond
        return SIf(iterable.cond,
            stream(iterable.then_branch, loop_var, body),
            stream(iterable.else_branch, loop_var, body))
    elif isinstance(iterable, EUnaryOp) and iterable.op == UOp.Distinct:
        tmp = fresh_var(TSet(iterable.type.elem_type), "distinct_elems")
        return seq([
            SDecl(tmp, EEmptyList().with_type(tmp.type)),
            stream(iterable.e, loop_var, SIf(
                ENot(EBinOp(loop_var, BOp.In, tmp).with_type(BOOL)),
                seq([body, SCall(tmp, "add", [loop_var])]),
                SNoOp()))])
    elif isinstance(iterable, EBinOp) and iterable.op == "+":
        return seq([
            stream(iterable.e1, loop_var, body),
            stream(iterable.e2, loop_var, body)])
    elif isinstance(iterable, EBinOp) and iterable.op == "-":
        raise NotImplementedError()
        # t = TList(iterable.type.elem_type)
        # e = self.visit(EBinOp(iterable.e1, "-", iterable.e2).with_type(t))
        # return stream(EEscape(e, (), ()).with_type(t), body)
    elif isinstance(iterable, EFilter):
        return stream(
            EFlatMap(iterable.e, ELambda(iterable.predicate.arg,
                ECond(iterable.predicate.body,
                    ESingleton(iterable.predicate.arg).with_type(iterable.type),
                    EEmptyList().with_type(iterable.type)).with_type(iterable.type))).with_type(iterable.type),
            loop_var,
            body)
        # test_setup, test_res = simplify_and_optimize_expression(iterable.predicate.apply_to(loop_var))
        # return stream(iterable.e, loop_var,
        #     seq([test_setup, SIf(test_res, body, SNoOp())]))
    elif isinstance(iterable, EMap):
        return stream(
            EFlatMap(iterable.e, ELambda(iterable.transform_function.arg,
                ESingleton(iterable.transform_function.body).with_type(iterable.type))).with_type(iterable.type),
            loop_var,
            body)
        # return stream(
        #     iterable.e,
        #     lambda v: body(iterable.transform_function.apply_to(v)))
    elif isinstance(iterable, EFlatMap):
        return stream(
            iterable.e,
            iterable.transform_function.arg,
            stream(iterable.transform_function.body, loop_var, body))
        # v = fresh_var(iterable.type.elem_type)
        # new_body = body(v)
        # assert isinstance(new_body, Stm)
        # return stream(iterable.e,
        #     body=lambda bag: SForEach(v, iterable.transform_function.apply_to(bag), new_body))
    elif isinstance(iterable, EListSlice):
        raise NotImplementedError()
        # s = fresh_var(INT, "start")
        # e = fresh_var(INT, "end")
        # l = self.visit(self.to_lvalue(iterable.e))
        # self.declare(s, EEscape("::std::max({start}, 0)", ("start",), (iterable.start,)))
        # self.declare(e, EEscape("::std::min({end}, static_cast<int>({it}.size()))", ("it", "end"), (iterable.e, iterable.end,)))
        # return self.visit(SWhile(ELt(s, e), SSeq(
        #     body(EEscape("{l}[{i}]", ("l", "i"), (iterable.e, s)).with_type(iterable.type.elem_type)),
        #     SAssign(s, EBinOp(s, "+", ONE).with_type(INT)))))
    elif isinstance(iterable, ELet):
        raise NotImplementedError()
        # return stream(iterable.body_function.apply_to(iterable.e), body)
    else:
        assert is_collection(iterable.type), repr(iterable)
        setup, e = simplify_and_optimize_expression(iterable)
        return SSeq(setup, SForEach(loop_var, e, simplify_and_optimize(body)))

def simplify_and_optimize(s : Stm) -> Stm:
    """Simplify and optimize a statement.

    Input:
      s - a statement to optimize

    Output:
      A statement that is functionally equivalent to the input.

    This function makes two big transformations:
      - "compile" many kinds of expressions (listed below) to simpler forms so
        that downstream code generation has less work to do
      - avoid creating short-lived intermediate objects (see `stream`)

    Expression types eliminated by this procedure:
      - EMap, EFilter, EFlatMap
      - EArg{Min,Max}
      - unary ops: Distinct
      - binary ops: In (where the collection is a Bag or List)
      - anything handled by an extension structure (see cozy.structures module)
      - EMakeMap2
    """
    assert isinstance(s, Stm)

    if isinstance(s, SNoOp):
        return s
    if isinstance(s, SSeq):
        return SSeq(simplify_and_optimize(s.s1), simplify_and_optimize(s.s2))
    if isinstance(s, SAssign):
        setup, e = simplify_and_optimize_expression(s.rhs)
        return SSeq(setup, SAssign(s.lhs, e))
    if isinstance(s, SDecl):
        setup, e = simplify_and_optimize_expression(s.val)
        return SSeq(setup, SDecl(s.var, e))
    if isinstance(s, SForEach):
        return stream(s.iter, s.loop_var, s.body)
    if isinstance(s, SEscape):
        return s
    if isinstance(s, SIf):
        setup, test = simplify_and_optimize_expression(s.cond)
        return SSeq(setup, SIf(test, simplify_and_optimize(s.then_branch), simplify_and_optimize(s.else_branch)))
    if isinstance(s, SScoped):
        return SScoped(simplify_and_optimize(s.s))
    if isinstance(s, SMapUpdate):
        return SMapUpdate(s.map, s.key, s.val_var, simplify_and_optimize(s.change))
    if isinstance(s, SCall):
        setups, args = zip(*(simplify_and_optimize_expression(a) for a in s.args))
        return seq(list(setups) + [SCall(s.target, s.func, tuple(args))])
    raise NotImplementedError(repr(s))

class ExpressionOptimizer(BottomUpRewriter):
    def __init__(self):
        super().__init__()
        self.stms = []

    def visit_iterable(self, e):
        res = fresh_var(e.type)
        self.stms.append(SDecl(res, EEmptyList().with_type(e.type)))
        x = fresh_var(e.type.elem_type)
        self.stms.append(simplify_and_optimize(SForEach(x, e, SCall(res, "add", (x,)))))
        return EMove(res).with_type(res.type)

    def visit_EFilter(self, e):
        return self.visit_iterable(e)

    def visit_EMap(self, e):
        return self.visit_iterable(e)

    def visit_EFlatMap(self, e):
        return self.visit_iterable(e)

    def visit_EUnaryOp(self, e):
        if e.op == UOp.Distinct:
            return self.visit_iterable(e)
        return self.visit_Exp(e)

    def visit_EMakeMap2(self, e):
        res = fresh_var(e.type, "map")
        self.stms.append(SDecl(res, EEmptyMap().with_type(e.type)))
        k = e.value_function.arg
        v = fresh_var(e.type.v, "v")
        self.stms.append(simplify_and_optimize(SForEach(k, e.e,
            SMapUpdate(res, k, v,
                SAssign(v, e.value_function.body)))))
        return EMove(res).with_type(res.type)

    def visit_Exp(self, e):
        if isinstance(e, Exp) and any(isinstance(child, ELambda) for child in e.children()):
            raise NotImplementedError(type(e))
        return super().visit_ADT(e)

def simplify_and_optimize_expression(e : Exp) -> (Stm, Exp):
    """Helper for simplify_and_optimize.

    Input:
      e - an expression to optimize

    Output:
      A pair (s, e') such that executing s and then evaluating e' is the same
      as evaluating the input expression.
    """
    optimizer = ExpressionOptimizer()
    e_prime = optimizer.visit(e)
    return (seq(optimizer.stms), e_prime)

def efficiently_reuseable(e : Exp) -> bool:
    if isinstance(e, EVar):
        return True
    return False

def re_use(value : Exp, v : EVar, s : Stm) -> Stm:
    if efficiently_reuseable(value) or count_occurrences_of_free_var(s, v) <= 1:
        return subst(s, {v.id : value})
    return seq([SDecl(v, value), s])
