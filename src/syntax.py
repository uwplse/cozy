"""
AST definitions.
"""

from common import ADT

def declare_case(supertype, name, attrs=()):
    """
    Usage: declare_case(SuperType, "CaseName", ["member1", ...])

    Creates a new class (CaseName) that is a subclass of SuperType and has all
    the given members.
    """
    class T(supertype):
        def __init__(self, *args):
            assert len(args) == len(attrs), "{} expects {} args, was given {}".format(name, len(attrs), len(args))
            for attr, val in zip(attrs, args):
                setattr(self, attr, val)
        def __str__(self):
            return repr(self)
        def __repr__(self):
            return "{}({})".format(name, ", ".join("{}={}".format(attr, repr(val)) for attr, val in zip(attrs, self.children())))
        def children(self):
            return tuple(getattr(self, a) for a in attrs)
    T.__name__ = name
    globals()[name] = T

declare_case(ADT, "Spec", ["name", "types", "statevars", "assumptions", "methods"])

class Method(ADT): pass
declare_case(Method, "Op",    ["name", "args", "assumptions", "body"])
declare_case(Method, "Query", ["name", "args", "assumptions", "ret"])

class Type(ADT): pass
declare_case(Type, "TInt")
declare_case(Type, "TBag",    ["t"])
declare_case(Type, "TList",   ["t"])
declare_case(Type, "TSet",    ["t"])
declare_case(Type, "TMap",    ["k", "v"])
declare_case(Type, "TNamed",  ["id"])
declare_case(Type, "TRecord", ["fields"])
declare_case(Type, "TApp",    ["t", "args"])
declare_case(Type, "TEnum",   ["cases"])

class Exp(ADT): pass
declare_case(Exp, "EVar",               ["id"])
declare_case(Exp, "EBool",              ["val"])
declare_case(Exp, "ENum",               ["val"])
declare_case(Exp, "EBinOp",             ["e1", "op", "e2"])
declare_case(Exp, "EUnaryOp",           ["op", "e"])
declare_case(Exp, "EGetField",          ["e", "f"])
declare_case(Exp, "EMakeRecord",        ["fields"])
declare_case(Exp, "EListComprehension", ["e", "clauses"])
declare_case(Exp, "EAlloc",             ["t", "args"])
declare_case(Exp, "ECall",              ["func", "args"])

class ComprehensionClause(ADT): pass
declare_case(ComprehensionClause, "CPull", ["id", "e"])
declare_case(ComprehensionClause, "CCond", ["e"])

class Stm(ADT): pass
declare_case(Stm, "SNoOp")
declare_case(Stm, "SCall",   ["target", "func", "args"])
declare_case(Stm, "SAssign", ["target", "field", "rhs"])
declare_case(Stm, "SDel",    ["e"])
