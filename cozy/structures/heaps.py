from cozy.common import fresh_name, declare_case
from cozy.syntax import *
from cozy.target_syntax import SWhile, SSwap, SSwitch, SEscapableBlock, SEscapeBlock, EMap, EFilter
from cozy.syntax_tools import fresh_var, pprint, shallow_copy
from cozy.pools import RUNTIME_POOL

from .arrays import TArray, EArrayGet, EArrayIndexOf, SArrayAlloc, SEnsureCapacity

# Key func is part of heap type
TMinHeap = declare_case(Type, "TMinHeap", ["t", "f"])
TMaxHeap = declare_case(Type, "TMaxHeap", ["t", "f"])

# Like EArgMin: bag, keyfunc
EMakeMinHeap = declare_case(Exp, "EMakeMinHeap", ["e", "f"])
EMakeMaxHeap = declare_case(Exp, "EMakeMaxHeap", ["e", "f"])

EHeapElems = declare_case(Exp, "EHeapElems", ["e"]) # all elements
EHeapPeek  = declare_case(Exp, "EHeapPeek",  ["e", "n"]) # look at min
EHeapPeek2 = declare_case(Exp, "EHeapPeek2", ["e", "n"]) # look at 2nd min

def to_heap(e : Exp) -> Exp:
    if isinstance(e, EArgMin):
        return EMakeMinHeap(e.e, e.f).with_type(TMinHeap(e.type, e.f))
    if isinstance(e, EArgMax):
        return EMakeMaxHeap(e.e, e.f).with_type(TMaxHeap(e.type, e.f))
    raise ValueError(e)

# Binary heap utilities
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

def find_func(e : Exp) -> ELambda:
    if isinstance(e, EMakeMinHeap) or isinstance(e, EMakeMaxHeap):
        return e.f
    raise NotImplementedError(e)

class Heaps(object):

    def owned_types(self):
        return (TMinHeap, TMaxHeap, EMakeMinHeap, EMakeMaxHeap, EHeapElems, EHeapPeek, EHeapPeek2)

    def default_value(self, t : Type) -> Exp:
        f = EMakeMinHeap if isinstance(t, TMinHeap) else EMakeMaxHeap
        x = EVar("x").with_type(t.t)
        return f(EEmptyList().with_type(TBag(t.t)), ELambda(x, x))

    def check_wf(self, e : Exp, state_vars : {EVar}, args : {EVar}, pool = RUNTIME_POOL, assumptions : Exp = T):
        from cozy.solver import valid
        if (isinstance(e, EHeapPeek) or isinstance(e, EHeapPeek2)):
            if pool != RUNTIME_POOL:
                return "heap peek in state position"
            if not valid(EEq(e.n, ELen(e.e))):
                return "invalid `n` parameter"
        return None

    def storage_size(self, e : Exp, k):
        assert type(e.type) in (TMinHeap, TMaxHeap)
        return k(EHeapElems(e).with_type(TBag(e.type.t)))

    def encoding_type(self, t : Type) -> Type:
        assert isinstance(t, TMaxHeap) or isinstance(t, TMinHeap)
        return TBag(TTuple((t.t, t.f.body.type)))

    def encode(self, e : Exp) -> Exp:
        if isinstance(e, EMakeMinHeap):
            tt = TTuple((e.f.arg.type, e.f.body.type))
            return EMap(e.e, ELambda(e.f.arg, ETuple((e.f.arg, e.f.body)).with_type(tt))).with_type(TBag(tt))
        elif isinstance(e, EMakeMaxHeap):
            tt = TTuple((e.f.arg.type, e.f.body.type))
            return EMap(e.e, ELambda(e.f.arg, ETuple((e.f.arg, e.f.body)).with_type(tt))).with_type(TBag(tt))
        elif isinstance(e, EHeapElems):
            arg = EVar(e.e.type.f.arg.id).with_type(TTuple((e.type.t, e.e.type.f.body.type)))
            return EMap(e.e, ELambda(arg, ETupleGet(arg, 0).with_type(e.type.t))).with_type(e.type)
        elif isinstance(e, EHeapPeek):
            f = EArgMin if isinstance(e.e.type, TMinHeap) else EArgMax
            return f(EHeapElems(e.e).with_type(TBag(e.type)), e.e.type.f).with_type(e.type)
        elif isinstance(e, EHeapPeek2):
            elem_type = e.e.type.t
            f = EArgMin if isinstance(e.e.type, TMinHeap) else EArgMax
            return f(EBinOp(EHeapElems(e.e).with_type(TBag(e.type)), "-", ESingleton(EHeapPeek(e.e, e.n).with_type(elem_type)).with_type(TBag(elem_type))).with_type(TBag(elem_type)), e.e.type.f).with_type(e.type)
        else:
            raise NotImplementedError(e)

    def mutate_in_place(self, lval, e, op, assumptions, make_subgoal):
        from cozy.incrementalization import mutate

        old_value = e
        new_value = mutate(e, op)

        # added/removed elements
        t = TBag(lval.type.t)
        old_elems = EHeapElems(old_value).with_type(t)
        new_elems = EHeapElems(new_value).with_type(t)
        initial_count = make_subgoal(ELen(old_elems))
        to_add = make_subgoal(EBinOp(new_elems, "-", old_elems).with_type(t), docstring="additions to {}".format(pprint(lval)))
        to_del_spec = EBinOp(old_elems, "-", new_elems).with_type(t)
        removed_count = make_subgoal(ELen(to_del_spec))
        to_del = make_subgoal(to_del_spec, docstring="deletions from {}".format(pprint(lval)))

        # modified elements
        f = lval.type.f
        v = fresh_var(t.t)
        old_v_key = f.apply_to(v)
        new_v_key = mutate(old_v_key, op)
        mod_spec = EFilter(old_elems, ELambda(v, EAll([EIn(v, new_elems), ENot(EEq(new_v_key, old_v_key))]))).with_type(new_elems.type)
        modified = make_subgoal(mod_spec)
        return seq([
            SCall(lval, "remove_all", (initial_count, to_del)),
            SCall(lval, "add_all",    (EBinOp(initial_count, "-", removed_count).with_type(INT), to_add)),
            SForEach(v, modified, SCall(lval, "update", (v, make_subgoal(new_v_key, a=[EIn(v, mod_spec)]))))])

    def rep_type(self, t : Type) -> Type:
        return TArray(t.t)

    def codegen(self, e : Exp, out : EVar) -> Stm:
        if isinstance(e, EMakeMinHeap) or isinstance(e, EMakeMaxHeap):
            out_raw = EVar(out.id).with_type(self.rep_type(e.type))
            l = fresh_var(INT, "alloc_len")
            x = fresh_var(e.type.t, "x")
            return seq([
                SDecl(l.id, ELen(e.e)),
                SArrayAlloc(out_raw, l),
                SCall(out, "add_all", (ZERO, e.e))])
        elif isinstance(e, EHeapElems):
            raise NotImplementedError()
        elif isinstance(e, EHeapPeek):
            raise NotImplementedError()
        elif isinstance(e, EHeapPeek2):
            from cozy.evaluation import construct_value
            best = EArgMin if isinstance(e.e.type, TMinHeap) else EArgMax
            f = e.e.type.f
            return SSwitch(e.n, (
                (ZERO, SAssign(out, construct_value(e.type))),
                (ONE,  SAssign(out, construct_value(e.type))),
                (TWO,  SAssign(out, EArrayGet(e.e, ONE).with_type(e.type)))),
                SAssign(out, best(EBinOp(ESingleton(EArrayGet(e.e, ONE).with_type(e.type)).with_type(TBag(out.type)), "+", ESingleton(EArrayGet(e.e, TWO).with_type(e.type)).with_type(TBag(out.type))).with_type(TBag(out.type)), f).with_type(out.type)))
        else:
            raise NotImplementedError(e)

    def implement_stmt(self, s : Stm) -> Stm:
        op = "<=" if isinstance(s.target.type, TMinHeap) else ">="
        f = s.target.type.f
        if isinstance(s, SCall):
            elem_type = s.target.type.t
            target_raw = EVar(s.target.id).with_type(self.rep_type(s.target.type))
            if s.func == "add_all":
                size = fresh_var(INT, "heap_size")
                i = fresh_var(INT, "i")
                x = fresh_var(elem_type, "x")
                return seq([
                    SDecl(size.id, s.args[0]),
                    SEnsureCapacity(target_raw, EBinOp(size, "+", ELen(s.args[1])).with_type(INT)),
                    SForEach(x, s.args[1], seq([
                        SAssign(EArrayGet(target_raw, size), x),
                        SDecl(i.id, size),
                        SWhile(EAll([
                            EBinOp(i, ">", ZERO).with_type(BOOL),
                            ENot(EBinOp(f.apply_to(EArrayGet(target_raw, _parent(i))), op, f.apply_to(EArrayGet(target_raw, i))).with_type(BOOL))]),
                            seq([
                                SSwap(EArrayGet(target_raw, _parent(i)), EArrayGet(target_raw, i)),
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
                    SDecl(size.id, s.args[0]),
                    SForEach(x, s.args[1], seq([
                        # find the element to remove
                        SDecl(i.id, EArrayIndexOf(target_raw, x).with_type(INT)),
                        # swap with last element in heap
                        SSwap(EArrayGet(target_raw, i), EArrayGet(target_raw, size_minus_one)),
                        # bubble down
                        SEscapableBlock(label, SWhile(_has_left_child(i, size_minus_one), seq([
                            SDecl(child_index.id, _left_child(i)),
                            SIf(EAll([_has_right_child(i, size_minus_one), ENot(EBinOp(f.apply_to(EArrayGet(target_raw, _left_child(i))), op, f.apply_to(EArrayGet(target_raw, _right_child(i)))))]),
                                SAssign(child_index, _right_child(i)),
                                SNoOp()),
                            SIf(ENot(EBinOp(f.apply_to(EArrayGet(target_raw, i)), op, f.apply_to(EArrayGet(target_raw, child_index)))),
                                seq([
                                    SSwap(EArrayGet(target_raw, i), EArrayGet(target_raw, child_index)),
                                    SAssign(i, child_index)]),
                                SEscapeBlock(label))]))),
                        # dec. size
                        SAssign(size, size_minus_one)]))])
            else:
                raise NotImplementedError()
        else:
            raise NotImplementedError(pprint(s))
