"""
AST definitions.
"""

from common import ADT, declare_case, typechecked

Spec                = declare_case(ADT, "Spec", ["name", "types", "statevars", "assumptions", "methods"])

class Method(ADT): pass
Op                  = declare_case(Method, "Op",    ["name", "args", "assumptions", "body"])
Query               = declare_case(Method, "Query", ["name", "args", "assumptions", "ret"])

class Type(ADT): pass
TInt                = declare_case(Type, "TInt")
TLong               = declare_case(Type, "TLong")
TBool               = declare_case(Type, "TBool")
TString             = declare_case(Type, "TString")
TNative             = declare_case(Type, "TNative", ["name"])
TMaybe              = declare_case(Type, "TMaybe", ["t"])
THandle             = declare_case(Type, "THandle", ["statevar", "value_type"])
TIterator           = declare_case(Type, "TIterator", ["t"])
TBag                = declare_case(Type, "TBag",    ["t"])
TList               = declare_case(Type, "TList",   ["t"])
TSet                = declare_case(Type, "TSet",    ["t"])
TMap                = declare_case(Type, "TMap",    ["k", "v"])
TNamed              = declare_case(Type, "TNamed",  ["id"])
TRecord             = declare_case(Type, "TRecord", ["fields"])
TApp                = declare_case(Type, "TApp",    ["t", "args"])
TEnum               = declare_case(Type, "TEnum",   ["cases"])
TTuple              = declare_case(Type, "TTuple",  ["ts"])

class Exp(ADT):
    def with_type(self, t):
        self.type = t
        return self
    # def __setattr__(self, name, val):
    #     if name == "type" and isinstance(self, EEnumEntry) and not isinstance(val, TEnum):
    #         raise Exception("set {}.type = {}".format(self, val))
    #     super().__setattr__(name, val)
    # def __getattr__(self, name):
    #     raise AttributeError("expression {} has no {} field".format(self, name))

EVar                = declare_case(Exp, "EVar",               ["id"])
EBool               = declare_case(Exp, "EBool",              ["val"])
ENum                = declare_case(Exp, "ENum",               ["val"])
EEnumEntry          = declare_case(Exp, "EEnumEntry",         ["name"])
ENull               = declare_case(Exp, "ENull")
ECond               = declare_case(Exp, "ECond",              ["cond", "then_branch", "else_branch"])
EBinOp              = declare_case(Exp, "EBinOp",             ["e1", "op", "e2"])
EUnaryOp            = declare_case(Exp, "EUnaryOp",           ["op", "e"])
EGetField           = declare_case(Exp, "EGetField",          ["e", "f"])
EMakeRecord         = declare_case(Exp, "EMakeRecord",        ["fields"])
EListComprehension  = declare_case(Exp, "EListComprehension", ["e", "clauses"])
EEmptyList          = declare_case(Exp, "EEmptyList")
ECall               = declare_case(Exp, "ECall",              ["func", "args"])
ETuple              = declare_case(Exp, "ETuple",             ["es"])
ETupleGet           = declare_case(Exp, "ETupleGet",          ["e", "n"])
ELet                = declare_case(Exp, "ELet",               ["id", "e1", "e2"])

class ComprehensionClause(ADT): pass
CPull               = declare_case(ComprehensionClause, "CPull", ["id", "e"])
CCond               = declare_case(ComprehensionClause, "CCond", ["e"])

class Stm(ADT): pass
SNoOp               = declare_case(Stm, "SNoOp")
SSeq                = declare_case(Stm, "SSeq",     ["s1", "s2"])
SCall               = declare_case(Stm, "SCall",    ["target", "func", "args"])
SAssign             = declare_case(Stm, "SAssign",  ["lhs", "rhs"])
SDecl               = declare_case(Stm, "SDecl",    ["id", "val"])
SForEach            = declare_case(Stm, "SForEach", ["id", "iter", "body"])
SIf                 = declare_case(Stm, "SIf",      ["cond", "then_branch", "else_branch"])

# -----------------------------------------------------------------------------
# Various utilities

BOOL = TBool()

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

def EAll(exps):
    res = None
    for e in exps:
        if res is None:
            res = e
        else:
            res = EBinOp(res, "and", e).with_type(BOOL)
    if res is None:
        return EBool(True).with_type(BOOL)
    return res

def ENot(e):
    if isinstance(e, EUnaryOp) and e.op == "not":
        return e.e
    return EUnaryOp("not", e).with_type(BOOL)
