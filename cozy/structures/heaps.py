from cozy.common import declare_case
from cozy.syntax import *
from cozy.syntax_tools import fresh_var, pprint
from cozy.pools import RUNTIME_POOL

# Key func is part of heap type
TMinHeap = declare_case(Type, "TMinHeap", ["t", "f"])
TMaxHeap = declare_case(Type, "TMaxHeap", ["t", "f"])

# Like EArgMin: bag, keyfunc
EMakeMinHeap = declare_case(Exp, "EMakeMinHeap", ["e", "f"])
EMakeMaxHeap = declare_case(Exp, "EMakeMaxHeap", ["e", "f"])

EHeapElems = declare_case(Exp, "EHeapElems", ["e"]) # all elements
EHeapPeek = declare_case(Exp, "EHeapPeek", ["e"])   # look at min
EHeapPeek2 = declare_case(Exp, "EHeapPeek2", ["e"]) # look at 2nd min

class Heaps(object):

    def owned_types(self):
        return (TMinHeap, TMaxHeap, EMakeMinHeap, EMakeMaxHeap, EHeapElems, EHeapPeek, EHeapPeek2)

    def default_value(self, t : Type) -> Exp:
        f = EMakeMinHeap if isinstance(t, TMinHeap) else EMakeMaxHeap
        x = EVar("x").with_type(t.t)
        return f(EEmptyList().with_type(TBag(t.t)), ELambda(x, x))

    def check_wf(self, e : Exp, state_vars : {EVar}, args : {EVar}, pool = RUNTIME_POOL, assumptions : Exp = T):
        if (isinstance(e, EHeapPeek) or isinstance(e, EHeapPeek2)) and pool != RUNTIME_POOL:
            return "heap peek in state position"
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
            return f(EBinOp(e.e, "-", ESingleton(EHeapPeek(e.e).with_type(elem_type)).with_type(TBag(elem_type))).with_type(TBag(elem_type)), e.e.type.f).with_type(e.type)
        else:
            raise NotImplementedError()

    def incrementalize(self, lval, old_value, new_value, state_vars, make_subgoal):
        t = TBag(lval.type.t)
        to_add = make_subgoal(EBinOp(EHeapElems(new_value).with_type(t), "-", EHeapElems(old_value).with_type(t)).with_type(t), docstring="additions to {}".format(pprint(lval)))
        to_del = make_subgoal(EBinOp(EHeapElems(old_value).with_type(t), "-", EHeapElems(new_value).with_type(t)).with_type(t), docstring="deletions from {}".format(pprint(lval)))
        v = fresh_var(t.t)
        return seq([
            SForEach(v, to_del, SCall(lval, "remove", [v])),
            SForEach(v, to_add, SCall(lval, "add", [v]))])

    def codegen(self, e : Exp) -> Exp:
        raise NotImplementedError()
