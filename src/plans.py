from predicates import *
from common import ADT

class Plan(ADT):
    def toPredicate(self):
        pass
    def isSortedBy(self, fieldName):
        pass
    def isTrivial(self):
        return False
    def wellFormed(self):
        pass

class All(Plan):
    def toPredicate(self):
        return Bool(True)
    def isSortedBy(self, fieldName):
        return True
    def isTrivial(self):
        return True
    def wellFormed(self):
        return True

class Empty(Plan):
    def toPredicate(self):
        return Bool(False)
    def isSortedBy(self, fieldName):
        return True
    def isTrivial(self):
        return True
    def wellFormed(self):
        return True

class HashLookup(Plan):
    def __init__(self, plan, fieldName, varName):
        self.plan = plan
        self.fieldName = fieldName
        self.varName = varName
    def toPredicate(self):
        return And(self.plan.toPredicate(), Compare(Var(self.fieldName), Eq, Var(self.varName)))
    def isSortedBy(self, fieldName):
        return self.plan.isSortedBy(fieldName)
    def wellFormed(self):
        return (isinstance(self.plan, HashLookup) or isinstance(self.plan, All)) and self.plan.wellFormed()
    def children(self):
        return (self.plan, self.fieldName, self.varName)

class BinarySearch(Plan):
    def __init__(self, plan, fieldName, op, varName):
        self.plan = plan
        self.fieldName = fieldName
        self.op = op
        self.varName = varName
    def toPredicate(self):
        return And(self.plan.toPredicate(), Compare(Var(self.fieldName), self.op, Var(self.varName)))
    def isSortedBy(self, fieldName):
        return fieldName == self.fieldName
    def wellFormed(self):
        return self.plan.wellFormed() and self.plan.isSortedBy(self.fieldName)
    def children(self):
        return (self.plan, self.fieldName, self.op, self.varName)

class Filter(Plan):
    def __init__(self, plan, predicate):
        self.plan = plan
        self.predicate = predicate
    def toPredicate(self):
        return And(self.plan.toPredicate(), self.predicate)
    def isSortedBy(self, fieldName):
        return False
    def wellFormed(self):
        return self.plan.wellFormed()
    def children(self):
        return (self.plan, self.predicate)

class Intersect(Plan):
    def __init__(self, plan1, plan2):
        self.plan1 = plan1
        self.plan2 = plan2
    def toPredicate(self):
        return And(self.plan1.toPredicate(), self.plan2.toPredicate())
    def isSortedBy(self, fieldName):
        return False
    def wellFormed(self):
        return self.plan1.wellFormed() and self.plan2.wellFormed()
    def children(self):
        return (self.plan1, self.plan2)

class Union(Plan):
    def __init__(self, plan1, plan2):
        self.plan1 = plan1
        self.plan2 = plan2
    def toPredicate(self):
        return Or(self.plan1.toPredicate(), self.plan2.toPredicate())
    def isSortedBy(self, fieldName):
        return False
    def wellFormed(self):
        return self.plan1.wellFormed() and self.plan2.wellFormed()
    def children(self):
        return (self.plan1, self.plan2)
