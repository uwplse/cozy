"""
While the syntax module declares the core _input_ language, this module declares
additional syntax extensions that can appear in the _target_ language: the
primitives the tool can output and use during synthesis.
"""

from cozy.syntax import *
from cozy.common import declare_case, typechecked, fresh_name

# Lambdas
EApp = declare_case(Exp, "EApp", ["f", "arg"])
class ELambda(Exp):
    @typechecked
    def __init__(self, arg : EVar, body : Exp):
        self.arg = arg
        self.body = body
    def apply_to(self, arg):
        from cozy.syntax_tools import subst
        return subst(self.body, { self.arg.id : arg })
    def children(self):
        return (self.arg, self.body)
    def __repr__(self):
        return "ELambda{}".format(repr(self.children()))

# Misc
TRef       = declare_case(Type, "TRef", ["t"])
EEnumToInt = declare_case(Exp, "EEnumToInt", ["e"])
EBoolToInt = declare_case(Exp, "EBoolToInt", ["e"])
EStm       = declare_case(Exp, "EStm", ["stm", "e"])

def EIsSingleton(e):
    arg = EVar(fresh_name()).with_type(e.type.t)
    return EBinOp(EUnaryOp(UOp.Sum, EMap(e, ELambda(arg, ONE)).with_type(TBag(INT))).with_type(INT), "<=", ONE).with_type(BOOL)

# Maybe
EAlterMaybe = declare_case(Exp, "EAlterMaybe", ["e", "f"])

# Fixed-length vectors
TVector    = declare_case(Type, "TVector", ["t", "n"])
EVectorGet = declare_case(Exp, "EVectorGet", ["e", "i"])

# Iterators
SWhile   = declare_case(Stm, "SWhile", ["e", "body"])
SBreak   = declare_case(Stm, "SBreak")

# Bag transformations
EMap     = declare_case(Exp, "EMap", ["e", "f"])
EFilter  = declare_case(Exp, "EFilter", ["e", "p"])
EFlatten = declare_case(Exp, "EFlatten", ["e"]) # aka concat: Bag<Bag<T>> -> Bag<T>
EFlatMap = declare_case(Exp, "EFlatMap", ["e", "f"]) # EFlatMap(e, f) == EFlatten(EMap(e, f))

# Handle transformations
EWithAlteredValue = declare_case(Exp, "EWithAlteredValue", ["handle", "new_value"])

# Maps
EMakeMap   = declare_case(Exp, "EMakeMap", ["e", "key", "value"])
EMakeMap2  = declare_case(Exp, "EMakeMap2", ["e", "value"])
EMapGet    = declare_case(Exp, "EMapGet", ["map", "key"])
EMapKeys   = declare_case(Exp, "EMapKeys", ["e"])
SMapPut    = declare_case(Stm, "SMapPut", ["map", "key", "value"])
SMapDel    = declare_case(Stm, "SMapDel", ["map", "key"])
SMapUpdate = declare_case(Stm, "SMapUpdate", ["map", "key", "val_var", "change"])
