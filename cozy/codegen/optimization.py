"""Simplification and optimization for Cozy-generated implementations.

The key methods are
 - stream
 - simplify_and_optimize
 - simplify_and_optimize_expression
"""

from cozy.common import fresh_name
from cozy.syntax import (
    BOOL, INT, INT_BAG, TSet, THandle,
    Exp, ZERO, ONE, ETRUE, EFALSE, EVar, ENum, ELambda, ELet, ELen, ELt,
    ECond, EUnaryOp, UOp, EBinOp, BOp, ENot, EGt, EIn, min_of, max_of,
    EGetField, EListGet, EListSlice, EEmptyList, ESingleton,
    Stm, SAssign, SIf, SForEach, SNoOp, seq, SSeq, SDecl, SCall)
from cozy.target_syntax import (
    SSwap, SWhile, SReturn, SSwitch,
    EMap, EFilter, EFlatMap,
    TMap, EEmptyMap, EMapGet, SMapUpdate, SMapDel,
    SEscapableBlock, SEscapeBlock,
    SArrayAlloc, SArrayReAlloc, SEnsureCapacity)
from cozy.structures.treemultiset import SInsert, SErase
from cozy.syntax_tools import fresh_var, count_occurrences_of_free_var, subst, BottomUpRewriter, pprint, is_lvalue
from cozy.typecheck import is_collection, is_hashable
from cozy import evaluation

from .misc import SScoped, SEscape, EMove

def histogram(e : Exp) -> (Stm, EVar):
    """Compute a histogram of the elements in the iterable `e`.

    Returns an unoptimized statement that declares and constructs a histogram
    map and the fresh variable that got declared.
    """
    elem_type = e.type.elem_type
    h = fresh_var(TMap(elem_type, INT), "histogram")
    x = fresh_var(elem_type, "x")
    count = fresh_var(INT, "count")
    stm = seq([
        SDecl(h, EEmptyMap().with_type(h.type)),
        SForEach(x, e,
            SMapUpdate(h, x, count,
                SAssign(count, EBinOp(count, "+", ONE).with_type(INT))))])
    return (stm, h)

def stream(iterable : Exp, loop_var : EVar, body : Stm) -> Stm:
    """Convert an iterable expression to a streaming operation.

    Input:
      iterable - an expression with an iterable type (Bag, Set, or List), not
        yet optimized
      loop_var - a variable to use as the loop variable
      body - a statement to run on that variable, not yet optimized

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
        cond_setup, cond = simplify_and_optimize_expression(iterable.cond)
        return seq([
            cond_setup,
            SIf(cond,
                stream(iterable.then_branch, loop_var, body),
                stream(iterable.else_branch, loop_var, body))])
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
        if is_hashable(iterable.type.elem_type):
            h_setup, h = histogram(iterable.e2)
            val_ref = fresh_var(INT, "count")
            return seq([
                simplify_and_optimize(h_setup),
                stream(
                    iterable.e1,
                    loop_var,
                    SIf(EGt(EMapGet(h, loop_var).with_type(INT), ZERO),
                        SMapUpdate(h, loop_var, val_ref, SAssign(val_ref, EBinOp(val_ref, "-", ONE).with_type(INT))),
                        body))])
        else:
            rhs = fresh_var(iterable.e2.type, "bag_subtraction_right")
            return seq([
                simplify_and_optimize(SDecl(rhs, iterable.e2)),
                stream(
                    iterable.e1,
                    loop_var,
                    SIf(EIn(loop_var, rhs),
                        SCall(rhs, "remove", (loop_var,)),
                        body))])
    elif isinstance(iterable, EFilter):
        return stream(
            EFlatMap(iterable.e, ELambda(iterable.predicate.arg,
                ECond(iterable.predicate.body,
                    ESingleton(iterable.predicate.arg).with_type(iterable.type),
                    EEmptyList().with_type(iterable.type)).with_type(iterable.type))).with_type(iterable.type),
            loop_var,
            body)
    elif isinstance(iterable, EMap):
        return stream(
            EFlatMap(iterable.e, ELambda(iterable.transform_function.arg,
                ESingleton(iterable.transform_function.body).with_type(iterable.type))).with_type(iterable.type),
            loop_var,
            body)
    elif isinstance(iterable, EFlatMap):
        inner_loop_var = fresh_var(
            iterable.transform_function.arg.type,
            iterable.transform_function.arg.id)
        return stream(
            iterable.e,
            inner_loop_var,
            stream(iterable.transform_function.apply_to(inner_loop_var), loop_var, body))
    elif isinstance(iterable, EListSlice):
        elem_type = iterable.type.elem_type
        l = fresh_var(iterable.e.type, "list")
        s = fresh_var(INT, "start")
        e = fresh_var(INT, "end")
        return simplify_and_optimize(seq([
            SDecl(l, iterable.e),
            SDecl(s, max_of(iterable.start, ZERO)),
            SDecl(e, min_of(iterable.end, ELen(l))),
            SWhile(ELt(s, e), seq([
                SDecl(loop_var, EListGet(l, s).with_type(elem_type)),
                body,
                SAssign(s, EBinOp(s, "+", ONE).with_type(INT))]))]))
    elif isinstance(iterable, ELet):
        v = fresh_var(
            iterable.body_function.arg.type,
            iterable.body_function.arg.id)
        return seq([
            simplify_and_optimize(SDecl(v, iterable.e)),
            stream(iterable.body_function.apply_to(v), loop_var, body)])
    elif isinstance(iterable, EMove):
        return stream(iterable.e, loop_var, body)
    else:
        assert is_collection(iterable.type), repr(iterable)
        setup, e = simplify_and_optimize_expression(iterable)
        return seq([setup, SForEach(loop_var, e, simplify_and_optimize(body))])

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
      - unary ops:
        Distinct,
        AreUnique,
        Length, Sum, All, Any,
        Exists, Empty,
        The
      - binary ops:
        In (where the collection is a Bag or List)
        "-" on collections
        "+" on collections
      - EMakeMap2
      - ELet
      - EListSlice
      - EStm
    """
    assert isinstance(s, Stm)

    if isinstance(s, SNoOp):
        return s
    if isinstance(s, SSeq):
        # TODO: while the first basic statement in s1 is an SDecl, we should
        # apply `re_use` to perhaps eliminate or inline the declaration.
        return seq([simplify_and_optimize(s.s1), simplify_and_optimize(s.s2)])
    if isinstance(s, SAssign):
        setup, e = simplify_and_optimize_expression(s.rhs)
        return seq([setup, SAssign(s.lhs, e)])
    if isinstance(s, SReturn):
        setup, e = simplify_and_optimize_expression(s.e)
        return seq([setup, SReturn(e)])
    if isinstance(s, SDecl):
        setup, e = simplify_and_optimize_expression(s.val)
        return seq([setup, SDecl(s.var, e)])
    if isinstance(s, SForEach):
        return stream(s.iter, s.loop_var, s.body)
    if isinstance(s, SEscape):
        return s
    if isinstance(s, SIf):
        setup, test = simplify_and_optimize_expression(s.cond)
        if test == ETRUE:
            return simplify_and_optimize(s.then_branch)
        if test == EFALSE:
            return simplify_and_optimize(s.else_branch)
        return seq([setup, SIf(test, simplify_and_optimize(s.then_branch), simplify_and_optimize(s.else_branch))])
    if isinstance(s, SWhile):
        setup, cond = simplify_and_optimize_expression(s.e)
        if setup != SNoOp():
            # This is a problem because we don't want to duplicate the setup
            # condition.
            # TODO: introduce an SEscapableBlock/SEscapeBlock to do it right
            raise ValueError("oops! setup for condition {} is very long:\n{}".format(pprint(s.e), pprint(setup)))
        return SWhile(cond, simplify_and_optimize(s.body))
    if isinstance(s, SScoped):
        return SScoped(simplify_and_optimize(s.s))
    if isinstance(s, SMapUpdate):
        # TODO: optimize s.map & s.key
        # TODO: s.map must be optimized as an lvalue
        mapsetup, map = simplify_and_optimize_lvalue(s.map)
        keysetup, key = simplify_and_optimize_expression(s.key)
        return seq([
            mapsetup,
            keysetup,
            SMapUpdate(map, key, s.val_var, simplify_and_optimize(s.change))])
    if isinstance(s, SMapDel):
        mapsetup, map = simplify_and_optimize_lvalue(s.map)
        keysetup, key = simplify_and_optimize_expression(s.key)
        return seq([
            mapsetup,
            keysetup,
            SMapDel(map, key)])
    if isinstance(s, SCall):
        setups, args = zip(*(simplify_and_optimize_expression(a) for a in s.args))
        return seq(list(setups) + [SCall(s.target, s.func, tuple(args))])
    if isinstance(s, SEscapableBlock):
        return SEscapableBlock(s.label, simplify_and_optimize(s.body))
    if isinstance(s, SEscapeBlock):
        return s
    if isinstance(s, SArrayAlloc):
        setup, cap = simplify_and_optimize_expression(s.capacity)
        return seq([setup, SArrayAlloc(s.a, cap)])
    if isinstance(s, SArrayReAlloc):
        setup, cap = simplify_and_optimize_expression(s.new_capacity)
        return seq([setup, SArrayReAlloc(s.a, cap)])
    if isinstance(s, SEnsureCapacity):
        setup, cap = simplify_and_optimize_expression(s.capacity)
        return seq([setup, SEnsureCapacity(s.a, cap)])
    if isinstance(s, SSwap):
        # TODO: if we want to optimize the operands we will need a special
        # procedure that optimizes lvalues while preserving meaning... same
        # goes for SAssign case above.
        return s
    if isinstance(s, SSwitch):
        setup, e = simplify_and_optimize_expression(s.e)
        new_cases = [(case, simplify_and_optimize(stm)) for (case, stm) in s.cases]
        new_default = simplify_and_optimize(s.default)
        return seq([setup, SSwitch(e, new_cases, new_default)])
    if isinstance(s, SErase) or isinstance(s, SInsert):
        return s
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

    def visit_EStm(self, e):
        self.stms.append(simplify_and_optimize(e.stm))
        return self.visit(e.out_var)

    def min_or_max(self, op, e, f):
        if isinstance(e, EBinOp) and e.op == "+" and isinstance(e.e1, ESingleton) and isinstance(e.e2, ESingleton):
            # argmin_f ([a] + [b]) ---> f(a) < f(b) ? a : b
            return self.visit(ECond(
                EBinOp(f.apply_to(e.e1.e), op, f.apply_to(e.e2.e)).with_type(BOOL),
                e.e1.e,
                e.e2.e).with_type(e.e1.e.type))
        out = fresh_var(e.type.elem_type, "min" if op == "<" else "max")
        first = fresh_var(BOOL, "first")
        x = fresh_var(e.type.elem_type, "x")
        decl1 = SDecl(out, evaluation.construct_value(out.type))
        decl2 = SDecl(first, ETRUE)
        find = SForEach(x, e,
            SIf(EBinOp(
                    first,
                    BOp.Or,
                    EBinOp(f.apply_to(x), op, f.apply_to(out)).with_type(BOOL)).with_type(BOOL),
                seq([SAssign(first, EFALSE), SAssign(out, x)]),
                SNoOp()))
        self.stms.append(simplify_and_optimize(seq([decl1, decl2, find])))
        return out

    def visit_EArgMin(self, e):
        return self.min_or_max("<", e.e, e.key_function)

    def visit_EArgMax(self, e):
        return self.min_or_max(">", e.e, e.key_function)

    def find_one(self, iterable):
        v = fresh_var(iterable.type.elem_type, "v")
        label = fresh_name("label")
        x = fresh_var(iterable.type.elem_type, "x")
        decl = SDecl(v, evaluation.construct_value(v.type))
        find = SEscapableBlock(label,
            SForEach(x, iterable, seq([
                SAssign(v, x),
                SEscapeBlock(label)])))
        self.stms.append(simplify_and_optimize(seq([decl, find])))
        return v

    def visit_EUnaryOp(self, e):
        op = e.op
        if op == UOp.Distinct:
            return self.visit_iterable(e)
        elif op == UOp.The:
            return self.find_one(e.e)
        elif op == UOp.Sum:
            sum_var = fresh_var(e.type, "sum")
            loop_var = fresh_var(e.e.type.elem_type, "x")
            self.stms.append(simplify_and_optimize(seq([
                SDecl(sum_var, ENum(0).with_type(e.type)),
                SForEach(loop_var, e.e,
                    SAssign(sum_var, EBinOp(sum_var, "+", loop_var).with_type(INT)))])))
            return sum_var
        elif op == UOp.All:
            arg = EVar("x").with_type(e.e.type.elem_type)
            return self.visit(EUnaryOp(UOp.Empty, EFilter(e.e, ELambda(arg, ENot(arg))).with_type(INT_BAG)).with_type(INT))
        elif op == UOp.Any:
            arg = EVar("x").with_type(e.e.type.elem_type)
            return self.visit(EUnaryOp(UOp.Exists, EFilter(e.e, ELambda(arg, arg)).with_type(INT_BAG)).with_type(INT))
        elif op == UOp.Empty:
            iterable = e.e
            v = fresh_var(BOOL, "v")
            label = fresh_name("label")
            x = fresh_var(iterable.type.elem_type, "x")
            decl = SDecl(v, ETRUE)
            find = SEscapableBlock(label,
                SForEach(x, iterable, seq([
                    SAssign(v, EFALSE),
                    SEscapeBlock(label)])))
            self.stms.append(simplify_and_optimize(seq([decl, find])))
            return v
        elif op == UOp.Exists:
            return self.visit(ENot(EUnaryOp(UOp.Empty, e.e).with_type(BOOL)))
        # elif op == UOp.AreUnique:
        #     s = fresh_var(TSet(e.e.type.elem_type), "unique_elems")
        #     u = fresh_var(BOOL, "is_unique")
        #     x = fresh_var(e.e.type.elem_type)
        #     label = fresh_name("label")
        #     self.visit(seq([
        #         SDecl(s, EEmptyList().with_type(s.type)),
        #         SDecl(u, ETRUE),
        #         SEscapableBlock(label,
        #             SForEach(x, e.e,
        #                 SIf(EEscape("{s}.find({x}) != {s}.end()", ("s", "x"), (s, x)).with_type(BOOL),
        #                     seq([SAssign(u, EFALSE), SEscapeBlock(label)]),
        #                     SEscape("{indent}{s}.insert({x});\n", ("s", "x"), (s, x)))))]))
        #     return u.id

        return self.visit_Exp(e)

    def visit_EBinOp(self, e):
        if e.op in ("+", "-") and is_collection(e.type):
            return self.visit_iterable(e)
        elif e.op == BOp.In and not isinstance(e.e2.type, TSet):
            t = BOOL
            res = fresh_var(t, "found")
            x = fresh_var(e.e1.type, "x")
            label = fresh_name("label")
            self.stms.append(simplify_and_optimize(seq([
                SDecl(res, EFALSE),
                SEscapableBlock(label,
                    SForEach(x, e.e2, SIf(
                        EBinOp(x, "==", e.e1).with_type(BOOL),
                        seq([SAssign(res, ETRUE), SEscapeBlock(label)]),
                        SNoOp())))])))
            return res
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

    def visit_ELet(self, e):
        value_exp = self.visit(e.e)
        fv = fresh_var(value_exp.type, e.body_function.arg.id)
        self.stms.append(SDecl(fv, value_exp))
        return self.visit(subst(e.body_function.body, { e.body_function.arg.id : fv }))

    def visit_ECond(self, e):
        v = fresh_var(e.type, "conditional_result")
        self.stms.append(simplify_and_optimize(seq([
            SDecl(v, evaluation.construct_value(e.type)),
            SIf(e.cond, SAssign(v, e.then_branch), SAssign(v, e.else_branch))])))
        return v

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

def simplify_and_optimize_lvalue(e : Exp) -> (Stm, Exp):
    """Helper for simplify_and_optimize.

    Input:
      e - an L-value expression to optimize

    Output:
      A pair (s, e') such that executing s and then evaluating e' is the same
      as evaluating the input expression.

    Unlike `simplify_and_optimize_expression`, this function preserves the
    meaning of `e` as an L-value.  For instance, this function will not replace
    `e` with a fresh variable.
    """
    assert is_lvalue(e), "not an L-value: {}".format(pprint(e))
    if isinstance(e, EVar):
        return (SNoOp(), e)
    if isinstance(e, EGetField):
        if isinstance(e.e.type, THandle):
            setup, handle = simplify_and_optimize_expression(e.e)
            return (setup, EGetField(handle, e.field_name).with_type(e.type))
        else:
            setup, lvalue = simplify_and_optimize_lvalue(e.e)
            return (setup, EGetField(lvalue, e.field_name).with_type(e.type))
    if isinstance(e, EMapGet):
        mapsetup, map = simplify_and_optimize_lvalue(e.map)
        keysetup, key = simplify_and_optimize_expression(e.key)
        return (seq([mapsetup, keysetup]), EMapGet(map, key).with_type(e.type))
    if isinstance(e, EListGet):
        listsetup, list_lvalue = simplify_and_optimize_lvalue(e.e)
        indexsetup, index_exp = simplify_and_optimize_expression(e.index)
        return (seq([listsetup, indexsetup]), EListGet(list_lvalue, index_exp).with_type(e.type))
    raise NotImplementedError(repr(e))

def efficiently_reuseable(e : Exp) -> bool:
    if isinstance(e, EVar):
        return True
    return False

def re_use(value : Exp, v : EVar, s : Stm) -> Stm:
    if efficiently_reuseable(value) or count_occurrences_of_free_var(s, v) <= 1:
        return subst(s, {v.id : value})
    return seq([SDecl(v, value), s])
