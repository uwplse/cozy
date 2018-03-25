from cozy.common import declare_case
from cozy.syntax import *
from cozy.syntax_tools import pprint

# Key func is part of heap type
TMinHeap = declare_case(Type, "TMinHeap", ["t", "f"])
TMaxHeap = declare_case(Type, "TMaxHeap", ["t", "f"])

# Like EArgMin: bag, keyfunc
EMakeMinHeap = declare_case(Exp, "EMakeMinHeap", ["e", "f"])
EMakeMaxHeap = declare_case(Exp, "EMakeMaxHeap", ["e", "f"])

EHeapPeek = declare_case(Exp, "EHeapPeek", ["e"])   # look at min
EHeapPeek2 = declare_case(Exp, "EHeapPeek2", ["e"]) # look at 2nd min

class Heaps(object):
    def owned_types(self):
        return (TMinHeap, TMaxHeap, EMakeMinHeap, EMakeMaxHeap, EHeapPeek, EHeapPeek2)
    def default_value(self, t : Type) -> Exp:
        f = EMakeMinHeap if isinstance(t, TMinHeap) else EMakeMaxHeap
        x = EVar("x").with_type(t.t)
        return f(EEmptyList().with_type(TBag(t.t)), ELambda(x, x))
    def encode(self, e : Exp) -> Exp:
        if isinstance(e, EMakeMinHeap):
            return e.e
        elif isinstance(e, EMakeMaxHeap):
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
    def codegen(self, e : Exp) -> Exp:
        raise NotImplementedError()
