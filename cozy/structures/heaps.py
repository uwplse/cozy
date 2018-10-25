from cozy.common import fresh_name, declare_case, No, pick_to_sum
from cozy.syntax import *
from cozy.target_syntax import SWhile, SSwap, SSwitch, SEscapableBlock, SEscapeBlock, EMap, EFilter, EStateVar
from cozy.syntax_tools import fresh_var, pprint, mk_lambda, alpha_equivalent
from cozy.pools import Pool, RUNTIME_POOL, STATE_POOL

from .arrays import TArray, EArrayGet, EArrayIndexOf, SArrayAlloc, SEnsureCapacity, EArrayLen, EArrayList

TMinHeap = declare_case(Type, "TMinHeap", ["elem_type", "key_type"])
TMaxHeap = declare_case(Type, "TMaxHeap", ["elem_type", "key_type"])

# Like EArgMin: bag, keyfunc
EMakeMinHeap = declare_case(Exp, "EMakeMinHeap", ["e", "key_function"])
EMakeMaxHeap = declare_case(Exp, "EMakeMaxHeap", ["e", "key_function"])

EHeapElems = declare_case(Exp, "EHeapElems", ["e"]) # all elements
EHeapPeek  = declare_case(Exp, "EHeapPeek",  ["e"]) # look at min
EHeapPeek2 = declare_case(Exp, "EHeapPeek2", ["e"]) # look at 2nd min

def to_heap(e : Exp) -> Exp:
    """Construct a heap that would be useful for evaluating `e`.

    Given an EArgMin or EArgMax expression, this function produces a new
    expression that constructs a heap. Peeking the top value of the
    constructed heap is semantically equivalent to evaluating `e`.
    """
    if isinstance(e, EArgMin):
        elem_type = e.type
        key_type = e.key_function.body.type
        return EMakeMinHeap(e.e, e.key_function).with_type(TMinHeap(elem_type, key_type))
    if isinstance(e, EArgMax):
        elem_type = e.type
        key_type = e.key_function.body.type
        return EMakeMaxHeap(e.e, e.key_function).with_type(TMaxHeap(elem_type, key_type))
    raise ValueError(e)

# Binary heap-index utilities.  Each takes an index and returns an index,
# and thus is independent of the heap itself.
def _left_child(idx : Exp) -> Exp:
    return EBinOp(EBinOp(idx, "<<", ONE).with_type(INT), "+", ONE).with_type(INT)
def _has_left_child(idx : Exp, size : Exp) -> Exp:
    return ELt(_left_child(idx), size)
def _right_child(idx : Exp) -> Exp:
    return EBinOp(EBinOp(idx, "<<", ONE).with_type(INT), "+", TWO).with_type(INT)
def _has_right_child(idx : Exp, size : Exp) -> Exp:
    return ELt(_right_child(idx), size)
def _parent(idx : Exp) -> Exp:
    return EBinOp(EBinOp(idx, "-", ONE).with_type(INT), ">>", ONE).with_type(INT)

def heap_func(e : Exp, concretization_functions : { str : Exp } = None) -> ELambda:
    """
    Assuming 'e' produces a heap, this returns the function used to sort its elements.
    """
    if isinstance(e, EMakeMinHeap) or isinstance(e, EMakeMaxHeap):
        return e.key_function
    if isinstance(e, EVar) and concretization_functions:
        ee = concretization_functions.get(e.id)
        if ee is not None:
            return heap_func(ee)
    if isinstance(e, ECond):
        h1 = heap_func(e.then_branch)
        h2 = heap_func(e.else_branch)
        if alpha_equivalent(h1, h2):
            return h1
        v = fresh_var(h1.arg.type)
        return ELambda(v, ECond(e.cond, h1.apply_to(v), h2.apply_to(v)).with_type(h1.body.type))
    raise NotImplementedError(repr(e))

class Heaps(object):

    def owned_types(self):
        return (TMinHeap, TMaxHeap, EMakeMinHeap, EMakeMaxHeap, EHeapElems, EHeapPeek, EHeapPeek2)

    def enumerate(self, context, size, pool, enumerate_subexps, enumerate_lambdas):
        from cozy.typecheck import is_ordered, is_collection

        if pool == STATE_POOL:
            for (sz1, sz2) in pick_to_sum(2, size-1):
                for e in enumerate_subexps(context, sz1, pool):
                    if is_collection(e.type):
                        elem_type = e.type.elem_type
                        for keyfunc in enumerate_lambdas(e, pool, sz2):
                            key_type = keyfunc.body.type
                            if is_ordered(key_type):
                                yield EMakeMinHeap(e, keyfunc).with_type(TMinHeap(elem_type, key_type))
                                yield EMakeMaxHeap(e, keyfunc).with_type(TMaxHeap(elem_type, key_type))

        elif pool == RUNTIME_POOL:
            for e in enumerate_subexps(context.root(), size-1, STATE_POOL):
                t = e.type
                if isinstance(t, TMinHeap) or isinstance(t, TMaxHeap):
                    elem_type = t.elem_type
                    # yielding EHeapElems would be redundant
                    yield EHeapPeek (EStateVar(e).with_type(e.type)).with_type(elem_type)
                    yield EHeapPeek2(EStateVar(e).with_type(e.type)).with_type(elem_type)

    def default_value(self, t : Type, default_value) -> Exp:
        """Construct a default value of the given type.

        The `default_value` parameter should be used to recursively construct
        a default value of a child type.
        """

        f = EMakeMinHeap if isinstance(t, TMinHeap) else EMakeMaxHeap
        x = EVar("x").with_type(t.elem_type)
        return f(EEmptyList().with_type(TBag(t.elem_type)), ELambda(x, default_value(t.key_type))).with_type(t)

    def check_wf(self, e : Exp, is_valid, state_vars : {EVar}, args : {EVar}, pool = RUNTIME_POOL, assumptions : Exp = ETRUE):
        """Return None or a string indicating a well-formedness error."""
        return None

    def possibly_useful(self,
            e           : Exp,
            context,
            pool        : Pool,
            assumptions : Exp,
            ops         : [Op],
            solver) -> bool:
        if isinstance(e, EHeapPeek) or isinstance(e, EHeapPeek2):
            if pool != RUNTIME_POOL:
                return No("heap peek in state position")
        return True

    def typecheck(self, e : Exp, typecheck, report_err):
        """Typecheck expression `e`.

        This function must write a type to `e.type` or call `report_err` to
        indicate a type error.  It is allowed to do both.

        The `typecheck` parameter should be used to make a recursive call to
        typecheck child nodes.
        """
        if isinstance(e, EMakeMaxHeap) or isinstance(e, EMakeMinHeap):
            typecheck(e.e)
            e.key_function.arg.type = e.e.type.elem_type
            typecheck(e.key_function)
            e.type = TMinHeap(e.e.type.elem_type, e.key_function.body.type)
        elif isinstance(e, EHeapPeek) or isinstance(e, EHeapPeek2):
            typecheck(e.e)
            ok = True
            if not (isinstance(e.e.type, TMinHeap) or isinstance(e.e.type, TMaxHeap)):
                report_err(e, "cannot peek a non-heap")
                ok = False
            if ok:
                e.type = e.e.type.elem_type
        elif isinstance(e, EHeapElems):
            typecheck(e.e)
            if isinstance(e.e.type, TMinHeap) or isinstance(e.e.type, TMaxHeap):
                e.type = TBag(e.e.type.elem_type)
            else:
                report_err(e, "cannot get heap elems of non-heap")
        else:
            raise NotImplementedError(e)

    def storage_size(self, e : Exp, storage_size) -> Exp:
        """Compute the storage size (in bytes) of the given expression.

        The `storage_size` parameter should be used to recursively compute
        storage sizes for other expressions.
        """
        assert type(e.type) in (TMinHeap, TMaxHeap)
        return storage_size(EHeapElems(e).with_type(TBag(e.type.elem_type)))

    def maintenance_cost(self,
            old_value           : Exp,
            new_value           : Exp,
            op                  : Op,
            storage_size,
            maintenance_cost,
            freebies            : [Exp] = []):
        assert type(e.type) in (TMinHeap, TMaxHeap)

        # added/removed elements
        t = TBag(e.type.elem_type)
        old_elems = EHeapElems(old_value).with_type(t)
        new_elems = EHeapElems(new_value).with_type(t)

        # Add these
        elems_added = storage_size(
            EBinOp(new_elems, "-", old_elems).with_type(t), freebies).with_type(INT)
        elems_rmved = storage_size(
            EBinOp(old_elems, "-", new_elems).with_type(t), freebies).with_type(INT)

        # modified elements
        f1 = heap_func(old_value)
        f2 = heap_func(new_value)
        v = fresh_var(t.elem_type)
        old_v_key = f1.apply_to(v)
        new_v_key = f2.apply_to(v)

        modified_elems = EFilter(old_elems, ELambda(v, EAll([EIn(v, new_elems), ENot(EEq(new_v_key, old_v_key))]))).with_type(new_elems.type)

        modified_cost = EUnaryOp(
            UOp.Sum,
            EMap(
                modified_elems,
                ELambda(
                    v,
                    maintenance_cost(
                        new_v_key, op, freebies)).with_type(INT)).with_type(INT)).with_type(INT_BAG)

        return ESum([elems_added, elems_rmved, modified_cost])

    def encoding_type(self, t : Type) -> Type:
        assert isinstance(t, TMaxHeap) or isinstance(t, TMinHeap)
        # bag of (elem, key(elem)) pairs
        return TBag(TTuple((t.elem_type, t.key_type)))

    def encode(self, e : Exp) -> Exp:
        """Convert an expression about heaps to one about bags."""
        if isinstance(e, EMakeMinHeap):
            tt = TTuple((e.type.elem_type, e.type.key_type))
            return EMap(e.e, ELambda(e.key_function.arg, ETuple((e.key_function.arg, e.key_function.body)).with_type(tt))).with_type(TBag(tt))
        elif isinstance(e, EMakeMaxHeap):
            tt = TTuple((e.type.elem_type, e.type.key_type))
            return EMap(e.e, ELambda(e.key_function.arg, ETuple((e.key_function.arg, e.key_function.body)).with_type(tt))).with_type(TBag(tt))
        elif isinstance(e, EHeapElems):
            tt = TTuple((e.e.type.elem_type, e.e.type.key_type))
            return EMap(e.e, mk_lambda(tt, lambda arg: ETupleGet(arg, 0).with_type(e.type.elem_type))).with_type(e.type)
        elif isinstance(e, EHeapPeek):
            tt = TTuple((e.e.type.elem_type, e.e.type.key_type))
            f = EArgMin if isinstance(e.e.type, TMinHeap) else EArgMax
            return nth_func(tt, 0).apply_to(f(e.e, nth_func(tt, 1)).with_type(tt))
        elif isinstance(e, EHeapPeek2):
            tt = TTuple((e.e.type.elem_type, e.e.type.key_type))
            f = EArgMin if isinstance(e.e.type, TMinHeap) else EArgMax
            best = f(e.e, nth_func(tt, 1)).with_type(tt)
            return nth_func(tt, 0).apply_to(f(EBinOp(e.e, "-", ESingleton(best).with_type(TBag(tt))).with_type(TBag(tt)), nth_func(tt, 1)).with_type(tt))
        else:
            raise NotImplementedError(e)

    def mutate_in_place(self, lval, e, op, assumptions, invariants, make_subgoal):
        from cozy.state_maintenance import mutate

        old_value = e
        new_value = mutate(e, op)

        # added/removed elements
        t = TBag(lval.type.elem_type)
        old_elems = EHeapElems(old_value).with_type(t)
        new_elems = EHeapElems(new_value).with_type(t)
        initial_count = make_subgoal(ELen(old_elems))
        to_add = make_subgoal(EBinOp(new_elems, "-", old_elems).with_type(t), docstring="additions to {}".format(pprint(lval)))
        to_del_spec = EBinOp(old_elems, "-", new_elems).with_type(t)
        removed_count = make_subgoal(ELen(to_del_spec))
        to_del = make_subgoal(to_del_spec, docstring="deletions from {}".format(pprint(lval)))

        # modified elements
        f1 = heap_func(old_value)
        f2 = heap_func(new_value)
        v = fresh_var(t.elem_type)
        old_v_key = f1.apply_to(v)
        new_v_key = f2.apply_to(v)
        mod_spec = EFilter(old_elems, ELambda(v, EAll([EIn(v, new_elems), ENot(EEq(new_v_key, old_v_key))]))).with_type(new_elems.type)
        modified = make_subgoal(mod_spec)
        intermediate_count = make_subgoal(EBinOp(ELen(old_elems), "-", ELen(to_del_spec)).with_type(INT))
        return seq([
            SCall(lval, "remove_all", (initial_count, to_del)),
            SCall(lval, "add_all",    (intermediate_count, to_add)),
            SForEach(v, modified, SCall(lval, "update", (v, make_subgoal(new_v_key, a=[EIn(v, mod_spec)]))))])

    def rep_type(self, t : Type) -> Type:
        return TTuple((INT, TArray(t.elem_type)))

    def codegen(self, e : Exp, concretization_functions : { str : Exp }, out : EVar) -> Stm:
        """Return statements that write the result of `e` to `out`.

        This function also requires the `concretization_functions` that
        describe the invariants for variables in `e`.
        """
        if isinstance(e, EMakeMinHeap) or isinstance(e, EMakeMaxHeap):
            out_raw = EVar(out.id).with_type(self.rep_type(e.type))
            elem_type = e.type.elem_type
            return seq([
                SAssign(out_raw, ETuple([ELen(e.e), EArrayList().with_type(TArray(elem_type))]).with_type(self.rep_type(e.type))),
                SArrayAlloc(ETupleGet(out_raw, 1).with_type(TArray(elem_type)), ELen(e.e)),
                SCall(out, "add_all", (ZERO, e.e))])
        elif isinstance(e, EHeapElems):
            elem_type = e.type.elem_type
            if isinstance(e.e, EMakeMinHeap) or isinstance(e.e, EMakeMaxHeap):
                x = fresh_var(elem_type, "x")
                return SForEach(x, e.e.e, SCall(out, "add", (x,)))
            i = fresh_var(INT, "i") # the array index
            return seq([
                SDecl(i, ZERO),
                SWhile(ELt(i, ETupleGet(e.e, 0).with_type(INT)), seq([
                    SCall(out, "add", (EArrayGet(ETupleGet(e.e, 1), i).with_type(elem_type),)),
                    SAssign(i, EBinOp(i, "+", ONE).with_type(INT))]))])
        elif isinstance(e, EHeapPeek):
            raise NotImplementedError()
        elif isinstance(e, EHeapPeek2):
            from cozy.evaluation import construct_value
            best = EArgMin if isinstance(e.e.type, TMinHeap) else EArgMax
            f = heap_func(e.e, concretization_functions)
            return SSwitch(ETupleGet(e.e, 0), (
                (ZERO, SAssign(out, construct_value(e.type))),
                (ONE,  SAssign(out, construct_value(e.type))),
                (TWO,  SAssign(out, EArrayGet(ETupleGet(e.e, 1), ONE).with_type(e.type)))),
                SAssign(out, best(EBinOp(ESingleton(EArrayGet(ETupleGet(e.e, 1), ONE).with_type(e.type)).with_type(TBag(out.type)), "+",
                                         ESingleton(EArrayGet(ETupleGet(e.e, 1), TWO).with_type(e.type)).with_type(TBag(out.type))).with_type(TBag(out.type)), f).with_type(out.type)))
        else:
            raise NotImplementedError(e)

    def implement_stmt(self, s : Stm, concretization_functions : { str : Exp }) -> Stm:
        """Convert a call to a heap function into simpler statements.

        This function also requires the `concretization_functions` that
        describe the invariants for variables in `e`.
        """

        comparison_op = "<=" if isinstance(s.target.type, TMinHeap) else ">="
        f = heap_func(s.target, concretization_functions)
        if isinstance(s, SCall):
            elem_type = s.target.type.elem_type
            target_raw = EVar(s.target.id).with_type(self.rep_type(s.target.type))
            target_len = ETupleGet(target_raw, 0).with_type(INT)
            target_array = ETupleGet(target_raw, 1).with_type(TArray(elem_type))
            if s.func == "add_all":
                size = fresh_var(INT, "heap_size")
                i = fresh_var(INT, "i")
                x = fresh_var(elem_type, "x")
                return seq([
                    SDecl(size, s.args[0]),
                    SEnsureCapacity(target_array, EBinOp(size, "+", ELen(s.args[1])).with_type(INT)),
                    SForEach(x, s.args[1], seq([
                        SAssign(target_len, EBinOp(target_len, "+", ONE).with_type(INT)),
                        SAssign(EArrayGet(target_array, size).with_type(elem_type), x),
                        SDecl(i, size),
                        SWhile(EAll([
                            EBinOp(i, ">", ZERO).with_type(BOOL),
                            ENot(EBinOp(f.apply_to(EArrayGet(target_array, _parent(i)).with_type(elem_type)), comparison_op, f.apply_to(EArrayGet(target_array, i).with_type(elem_type))).with_type(BOOL))]),
                            seq([
                                SSwap(EArrayGet(target_array, _parent(i)).with_type(elem_type), EArrayGet(target_array, i).with_type(elem_type)),
                                SAssign(i, _parent(i))])),
                        SAssign(size, EBinOp(size, "+", ONE).with_type(INT))]))])
            elif s.func == "remove_all":
                size = fresh_var(INT, "heap_size")
                size_minus_one = EBinOp(size, "-", ONE).with_type(INT)
                i = fresh_var(INT, "i")
                x = fresh_var(elem_type, "x")
                label = fresh_name("stop_bubble_down")
                child_index = fresh_var(INT, "child_index")
                return seq([
                    SDecl(size, s.args[0]),
                    SForEach(x, s.args[1], seq([
                        SAssign(target_len, EBinOp(target_len, "-", ONE).with_type(INT)),
                        # find the element to remove
                        SDecl(i, EArrayIndexOf(target_array, x).with_type(INT)),
                        # swap with last element in heap
                        SSwap(EArrayGet(target_array, i).with_type(elem_type), EArrayGet(target_array, size_minus_one).with_type(elem_type)),
                        # bubble down
                        SEscapableBlock(label, SWhile(_has_left_child(i, size_minus_one), seq([
                            SDecl(child_index, _left_child(i)),
                            SIf(EAll([_has_right_child(i, size_minus_one), ENot(EBinOp(f.apply_to(EArrayGet(target_array, _left_child(i)).with_type(elem_type)), comparison_op, f.apply_to(EArrayGet(target_array, _right_child(i)).with_type(elem_type))))]),
                                SAssign(child_index, _right_child(i)),
                                SNoOp()),
                            SIf(ENot(EBinOp(f.apply_to(EArrayGet(target_array, i).with_type(elem_type)), comparison_op, f.apply_to(EArrayGet(target_array, child_index).with_type(elem_type)))),
                                seq([
                                    SSwap(EArrayGet(target_array, i).with_type(elem_type), EArrayGet(target_array, child_index).with_type(elem_type)),
                                    SAssign(i, child_index)]),
                                SEscapeBlock(label))]))),
                        # dec. size
                        SAssign(size, size_minus_one)]))])
            else:
                raise ValueError("heaps do not support the function {}".format(s.func))
        else:
            raise ValueError("the statement {} is not an update to a heap variable".format(pprint(s)))
