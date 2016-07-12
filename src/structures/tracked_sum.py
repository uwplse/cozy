from .interface import ConcreteImpl
from common import fresh_name, typechecked
import syntax
import incrementalization as inc

INIT_CAPACITY = 8

class TrackedSum(ConcreteImpl):

    class Change(inc.Delta):
        def __init__(self, alter_by):
            self.alter_by = alter_by

    def __str__(self):
        return "TrackedSum"
    def __repr__(self):
        return self.__str__()

    def __init__(self, collection):
        self.collection = collection
        self.sum = syntax.EVar(fresh_name()).with_type(collection.result_type().t)

    def state(self):
        return [(self.sum.id, self.sum.type)]

    @typechecked
    def derivative(self, member : syntax.EVar, delta : inc.Delta):
        (d, goals) = self.collection.derivative(member, delta)
        return (self._on_delta(d), goals)

    def _on_delta(self, delta):
        if isinstance(delta, inc.NoDelta):
            return TrackedSum.Change(syntax.ENum(0))
        elif isinstance(delta, inc.SetAdd):
            return TrackedSum.Change(delta.e)
        elif isinstance(delta, inc.SetRemove):
            return TrackedSum.Change(syntax.EUnaryOp("-", delta.e))
        else:
            raise NotImplementedError(d)

    @typechecked
    def apply_change(self, delta : inc.Delta) -> syntax.Stm:
        return syntax.SAssign(self.sum, syntax.EBinOp(self.sum, "+", delta.alter_by))

    def query(self):
        return self.sum
