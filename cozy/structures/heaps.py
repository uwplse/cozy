from cozy.common import declare_case
from cozy.syntax import *
from cozy.target_syntax import SWhile, SSwap, SSwitch
from cozy.syntax_tools import fresh_var, pprint, shallow_copy
from cozy.pools import RUNTIME_POOL

from .arrays import TArray, EArrayCapacity, EArrayGet, SArrayAlloc, SEnsureCapacity

# Key func is part of heap type
TMinHeap = declare_case(Type, "TMinHeap", ["t", "f"])
TMaxHeap = declare_case(Type, "TMaxHeap", ["t", "f"])

# Like EArgMin: bag, keyfunc
EMakeMinHeap = declare_case(Exp, "EMakeMinHeap", ["e", "f"])
EMakeMaxHeap = declare_case(Exp, "EMakeMaxHeap", ["e", "f"])

EHeapElems = declare_case(Exp, "EHeapElems", ["e"]) # all elements
EHeapPeek  = declare_case(Exp, "EHeapPeek",  ["e", "n"]) # look at min
EHeapPeek2 = declare_case(Exp, "EHeapPeek2", ["e", "n"]) # look at 2nd min

# Binary heap utilities
def _left_child(idx : Exp) -> Exp:
    return EBinOp(EBinOp(idx, "<<", ONE).with_type(INT), "+", ONE).with_type(INT)
def _right_child(idx : Exp) -> Exp:
    return EBinOp(EBinOp(idx, "<<", ONE).with_type(INT), "+", TWO).with_type(INT)
def _parent(idx : Exp) -> Exp:
    return EBinOp(EBinOp(idx, "-", ONE).with_type(INT), ">>", ONE).with_type(INT)

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

    def encoding_type(self, t : Type) -> Type:
        assert isinstance(t, TMaxHeap) or isinstance(t, TMinHeap)
        return TBag(t.t)

    def encode(self, e : Exp) -> Exp:
        if isinstance(e, EMakeMinHeap):
            return e.e
        elif isinstance(e, EMakeMaxHeap):
            return e.e
        elif isinstance(e, EHeapElems):
            return e.e
        elif isinstance(e, EHeapPeek):
            f = EArgMin if isinstance(e.e.type, TMinHeap) else EArgMax
            return f(e.e, e.e.type.f).with_type(e.type)
        elif isinstance(e, EHeapPeek2):
            elem_type = e.e.type.t
            f = EArgMin if isinstance(e.e.type, TMinHeap) else EArgMax
            return f(EBinOp(e.e, "-", ESingleton(EHeapPeek(e.e, e.n).with_type(elem_type)).with_type(TBag(elem_type))).with_type(TBag(elem_type)), e.e.type.f).with_type(e.type)
        else:
            raise NotImplementedError()

    def incrementalize(self, lval, old_value, new_value, state_vars, make_subgoal):
        t = TBag(lval.type.t)
        old_elems = EHeapElems(old_value).with_type(t)
        new_elems = EHeapElems(new_value).with_type(t)
        initial_count = make_subgoal(ELen(old_elems))
        to_add = make_subgoal(EBinOp(new_elems, "-", old_elems).with_type(t), docstring="additions to {}".format(pprint(lval)))
        to_del_spec = EBinOp(old_elems, "-", new_elems).with_type(t)
        removed_count = make_subgoal(ELen(to_del_spec))
        to_del = make_subgoal(to_del_spec, docstring="deletions from {}".format(pprint(lval)))
        v = fresh_var(t.t)
        return seq([
            SCall(lval, "remove_all", (initial_count, to_del)),
            SCall(lval, "add_all",    (EBinOp(initial_count, "-", removed_count).with_type(INT), to_add))])

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
                return SNoOp() # TODO
            else:
                raise NotImplementedError()
        else:
            raise NotImplementedError(pprint(s))
