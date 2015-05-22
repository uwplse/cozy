import itertools
import z3
from common import ADT

class Predicate(ADT):
    def toNNF(self):
        return self
    def toZ3(self, context):
        pass
    def eval(self, env):
        pass
    def comparisons(self):
        """returns a stream of var, field tuples"""
        return ()
    def contains_disjunction(self):
        return any(p.contains_disjunction() for p in self.children() if isinstance(p, Predicate))
    def contains_conjunction(self):
        return any(p.contains_conjunction() for p in self.children() if isinstance(p, Predicate))
    def ops(self):
        return itertools.chain(*(p.ops() for p in self.children() if isinstance(p, Predicate)))
    def vars(self):
        return itertools.chain(*(p.vars() for p in self.children() if isinstance(p, Predicate)))

class Var(Predicate):
    def __init__(self, name):
        self.name = name
    def children(self):
        return (self.name,)
    def toZ3(self, context):
        return z3.Int(self.name, context)
    def eval(self, env):
        return env.get(self.name, 0)
    def vars(self):
        return (self,)
    def __str__(self):
        return self.name

class Bool(Predicate):
    def __init__(self, val):
        self.val = bool(val)
    def children(self):
        return (self.val,)
    def toZ3(self, context):
        return z3.BoolVal(self.val, context)
    def eval(self, env):
        return self.val
    def __str__(self):
        return str(self.val)

# operators
Eq = "Eq"
Ne = "Ne"
Gt = "Gt"
Ge = "Ge"
Lt = "Lt"
Le = "Le"
operators = (Eq, Ne, Gt, Ge, Lt, Le)

def invertOp(op):
    if op == Eq: return Ne
    if op == Ne: return Eq
    if op == Lt: return Ge
    if op == Le: return Gt
    if op == Gt: return Le
    if op == Ge: return Lt

def opToStr(op):
    if op == Eq: return "=="
    if op == Ne: return "!="
    if op == Lt: return "<"
    if op == Le: return "<="
    if op == Gt: return ">"
    if op == Ge: return ">="

def opToName(op):
    if op == Eq: return "Eq"
    if op == Ne: return "Ne"
    if op == Lt: return "Lt"
    if op == Le: return "Le"
    if op == Gt: return "Gt"
    if op == Ge: return "Ge"

class Compare(Predicate):
    def __init__(self, lhs, op, rhs):
        self.lhs = lhs
        self.op = op
        self.rhs = rhs
    def children(self):
        return (self.lhs, self.op, self.rhs)
    def toNNF(self):
        return Compare(self.lhs.toNNF(), self.op, self.rhs.toNNF())
    def toZ3(self, context):
        if self.op == Eq: return self.lhs.toZ3(context) == self.rhs.toZ3(context)
        if self.op == Ne: return self.lhs.toZ3(context) != self.rhs.toZ3(context)
        if self.op == Ge: return self.lhs.toZ3(context) >= self.rhs.toZ3(context)
        if self.op == Gt: return self.lhs.toZ3(context) >  self.rhs.toZ3(context)
        if self.op == Le: return self.lhs.toZ3(context) <= self.rhs.toZ3(context)
        if self.op == Lt: return self.lhs.toZ3(context) <  self.rhs.toZ3(context)
    def eval(self, env):
        if self.op == Eq: return self.lhs.eval(env) == self.rhs.eval(env)
        if self.op == Ne: return self.lhs.eval(env) != self.rhs.eval(env)
        if self.op == Ge: return self.lhs.eval(env) >= self.rhs.eval(env)
        if self.op == Gt: return self.lhs.eval(env) >  self.rhs.eval(env)
        if self.op == Le: return self.lhs.eval(env) <= self.rhs.eval(env)
        if self.op == Lt: return self.lhs.eval(env) <  self.rhs.eval(env)
    def comparisons(self):
        return [(self.lhs.name, self.rhs.name)]
    def ops(self):
        return (self.op,)
    def __str__(self):
        return "{} {} {}".format(self.lhs, opToStr(self.op), self.rhs)

class And(Predicate):
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs
    def children(self):
        return (self.lhs, self.rhs)
    def toNNF(self):
        return And(self.lhs.toNNF(), self.rhs.toNNF())
    def toZ3(self, context):
        return z3.And(self.lhs.toZ3(context), self.rhs.toZ3(context), context)
    def eval(self, env):
        return self.lhs.eval(env) and self.rhs.eval(env)
    def comparisons(self):
        for c in self.lhs.comparisons(): yield c
        for c in self.rhs.comparisons(): yield c
    def contains_conjunction(self):
        return True
    def __str__(self):
        return "({} and {})".format(self.lhs, self.rhs)

class Or(Predicate):
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs
    def children(self):
        return (self.lhs, self.rhs)
    def toNNF(self):
        return Or(self.lhs.toNNF(), self.rhs.toNNF())
    def toZ3(self, context):
        return z3.Or(self.lhs.toZ3(context), self.rhs.toZ3(context), context)
    def eval(self, env):
        return self.lhs.eval(env) or self.rhs.eval(env)
    def comparisons(self):
        for c in self.lhs.comparisons(): yield c
        for c in self.rhs.comparisons(): yield c
    def contains_disjunction(self):
        return True
    def __str__(self):
        return "({} or {})".format(self.lhs, self.rhs)

class Not(Predicate):
    def __init__(self, p):
        self.p = p
    def children(self):
        return (self.p,)
    def toNNF(self):
        if isinstance(self.p, Var):     return self
        if isinstance(self.p, Bool):    return Bool(not self.p.val)
        if isinstance(self.p, Compare): return Compare(self.p.lhs.toNNF(), invertOp(self.p.op), self.p.rhs.toNNF())
        if isinstance(self.p, And):     return Or(Not(self.p.lhs).toNNF(), Not(self.p.rhs).toNNF())
        if isinstance(self.p, Or):      return And(Not(self.p.lhs).toNNF(), Not(self.p.rhs).toNNF())
        if isinstance(self.p, Not):     return self.p.toNNF()
    def toZ3(self, context):
        return z3.Not(self.p, context)
    def eval(self, env):
        return not self.p.eval(env)
    def comparisons(self):
        return self.p.comparisons()
    def __str__(self):
        return "not {}".format(self.p)
