"""
AST definitions.
"""

from common import ADT, declare_case

Spec                = declare_case(ADT, "Spec", ["name", "types", "statevars", "assumptions", "methods"])

class Method(ADT): pass
Op                  = declare_case(Method, "Op",    ["name", "args", "assumptions", "body"])
Query               = declare_case(Method, "Query", ["name", "args", "assumptions", "ret"])

class Type(ADT): pass
TInt                = declare_case(Type, "TInt")
TLong               = declare_case(Type, "TLong")
TBool               = declare_case(Type, "TBool")
TString             = declare_case(Type, "TString")
THandle             = declare_case(Type, "THandle", ["t"])
TBag                = declare_case(Type, "TBag",    ["t"])
TList               = declare_case(Type, "TList",   ["t"])
TSet                = declare_case(Type, "TSet",    ["t"])
TMap                = declare_case(Type, "TMap",    ["k", "v"])
THeap               = declare_case(Type, "THeap",   ["t"])
TNamed              = declare_case(Type, "TNamed",  ["id"])
TRecord             = declare_case(Type, "TRecord", ["fields"])
TApp                = declare_case(Type, "TApp",    ["t", "args"])
TEnum               = declare_case(Type, "TEnum",   ["cases"])
TTuple              = declare_case(Type, "TTuple",  ["ts"])

class Exp(ADT): pass
EVar                = declare_case(Exp, "EVar",               ["id"])
EBool               = declare_case(Exp, "EBool",              ["val"])
ENum                = declare_case(Exp, "ENum",               ["val"])
EBinOp              = declare_case(Exp, "EBinOp",             ["e1", "op", "e2"])
EUnaryOp            = declare_case(Exp, "EUnaryOp",           ["op", "e"])
EGetField           = declare_case(Exp, "EGetField",          ["e", "f"])
EMakeRecord         = declare_case(Exp, "EMakeRecord",        ["fields"])
EListComprehension  = declare_case(Exp, "EListComprehension", ["e", "clauses"])
EEmptyList          = declare_case(Exp, "EEmptyList")
EAlloc              = declare_case(Exp, "EAlloc",             ["t", "args"])
ECall               = declare_case(Exp, "ECall",              ["func", "args"])
ETuple              = declare_case(Exp, "ETuple",             ["es"])
ELet                = declare_case(Exp, "ELet",               ["id", "e1", "e2"])

class ComprehensionClause(ADT): pass
CPull               = declare_case(ComprehensionClause, "CPull", ["id", "e"])
CCond               = declare_case(ComprehensionClause, "CCond", ["e"])

class Stm(ADT): pass
SNoOp               = declare_case(Stm, "SNoOp")
SSeq                = declare_case(Stm, "SSeq",     ["s1", "s2"])
SCall               = declare_case(Stm, "SCall",    ["target", "func", "args"])
SAssign             = declare_case(Stm, "SAssign",  ["lhs", "rhs"])
SDel                = declare_case(Stm, "SDel",     ["e"])
SForEach            = declare_case(Stm, "SForEach", ["id", "iter", "body"])

def seq(stms):
    stms = [s for s in stms if not isinstance(s, SNoOp)]
    if not stms:
        return SNoOp()
    elif len(stms) == 1:
        return stms[0]
    else:
        result = None
        for s in stms:
            result = s if result is None else SSeq(result, s)
        return result
