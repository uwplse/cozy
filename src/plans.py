from predicates import *
from common import ADT

class Plan(ADT):
    def toPredicate(self):
        pass
    def isSortedBy(self, fieldName):
        return False
    def isTrivial(self):
        return False
    def wellFormed(self, z3ctx, z3solver, fields, vars):
        pass

class AllWhere(Plan):
    def __init__(self, predicate):
        self.predicate = predicate
    def toPredicate(self):
        return self.predicate
    def isSortedBy(self, fieldName):
        return True
    def isTrivial(self):
        return True
    def wellFormed(self, *args):
        return True
    def children(self):
        return (self.predicate,)

class HashLookup(Plan):
    def __init__(self, plan, predicate):
        self.plan = plan
        self.predicate = predicate
    def toPredicate(self):
        return And(self.plan.toPredicate(), self.predicate)
    def isSortedBy(self, fieldName):
        return self.plan.isSortedBy(fieldName)
    def wellFormed(self, z3ctx, z3solver, fields, vars):
        if set(self.predicate.ops()) != {Eq}:
            return False
        disj = self.predicate.contains_disjunction()
        conj = self.predicate.contains_conjunction()
        if disj and conj:
            return False
        # if disj and len(set(v.name for v in self.predicate.vars()) & set(vars)) != 1:
        #     return False
        if disj:
            return False
        return (isinstance(self.plan, HashLookup) or isinstance(self.plan, AllWhere)) and self.plan.wellFormed(z3ctx, z3solver, fields, vars)
    def children(self):
        return (self.plan, self.predicate)

class BinarySearch(Plan):
    def __init__(self, plan, sortField, predicate):
        self.plan = plan
        self.sortField = sortField
        self.predicate = predicate
    def toPredicate(self):
        return And(self.plan.toPredicate(), self.predicate)
    def isSortedBy(self, fieldName):
        return self.sortField == fieldName
    def wellFormed(self, *args):
        ops = set(self.predicate.ops())
        if (ops & {Eq, Ne}) or not ops:
            return False
        if self.predicate.contains_disjunction():
            return False
        return self.sortField in (v.name for v in self.predicate.vars()) and self.plan.wellFormed(*args) and self.plan.isSortedBy(self.sortField)
    def children(self):
        return (self.plan, self.sortField, self.predicate)

class Filter(Plan):
    def __init__(self, plan, predicate):
        self.plan = plan
        self.predicate = predicate
    def toPredicate(self):
        return And(self.plan.toPredicate(), self.predicate)
    def wellFormed(self, *args):
        return self.plan.wellFormed(*args)
    def children(self):
        return (self.plan, self.predicate)
    def isSortedBy(self, fieldName):
        return self.plan.isSortedBy(fieldName)

class Intersect(Plan):
    def __init__(self, plan1, plan2):
        self.plan1 = plan1
        self.plan2 = plan2
    def toPredicate(self):
        return And(self.plan1.toPredicate(), self.plan2.toPredicate())
    def wellFormed(self, *args):
        return self.plan1.wellFormed(*args) and self.plan2.wellFormed(*args)
    def children(self):
        return (self.plan1, self.plan2)

class Union(Plan):
    def __init__(self, plan1, plan2):
        self.plan1 = plan1
        self.plan2 = plan2
    def toPredicate(self):
        return Or(self.plan1.toPredicate(), self.plan2.toPredicate())
    def wellFormed(self, *args):
        return self.plan1.wellFormed(*args) and self.plan2.wellFormed(*args)
    def children(self):
        return (self.plan1, self.plan2)

class Concat(Plan):
    def __init__(self, plan1, plan2):
        self.plan1 = plan1
        self.plan2 = plan2
    def toPredicate(self):
        return Or(self.plan1.toPredicate(), self.plan2.toPredicate())
    def wellFormed(self, z3ctx, z3solver, fields, vars):
        return (
            self.plan1.wellFormed(z3ctx, z3solver, fields, vars) and
            self.plan2.wellFormed(z3ctx, z3solver, fields, vars) and
            predicates_disjoint(z3ctx, z3solver, self.plan1.toPredicate(), self.plan2.toPredicate()))
    def children(self):
        return (self.plan1, self.plan2)

_memo = {}
def predicates_disjoint(z3ctx, z3solver, p1, p2):
    # memoize for speed
    key = (p1, p2)
    result = _memo.get(key)
    if result is not None:
        return result

    # ah crap, gotta call our solver
    z3solver.push()
    z3solver.add(p1.toZ3(z3ctx))
    z3solver.add(p2.toZ3(z3ctx))
    result = str(z3solver.check()) == "unsat"
    z3solver.pop()
    _memo[(p1, p2)] = _memo[(p2, p1)] = result
    return result
