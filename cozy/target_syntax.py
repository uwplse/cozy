"""Additional internal syntax.

While the syntax module declares the core _input_ language, this module declares
additional syntax extensions that can appear in the _target_ language: the
primitives the tool can output and use during synthesis.
"""

from cozy.syntax import *
from cozy.common import declare_case, fresh_name

# Misc
TRef       = declare_case(Type, "TRef", ["elem_type"])
EEnumToInt = declare_case(Exp, "EEnumToInt", ["e"])
EBoolToInt = declare_case(Exp, "EBoolToInt", ["e"])

# Execute a statement and then "return" the value of `out_var`.  The statement
# must declare `out_var` in its body.
EStm       = declare_case(Exp, "EStm", ["stm", "out_var"])

# State var barrier: sub-expression should be maintained as a fresh state var
EStateVar  = declare_case(Exp, "EStateVar", ["e"])

def EIsSingleton(e):
    arg = EVar(fresh_name()).with_type(e.type.elem_type)
    return EBinOp(EUnaryOp(UOp.Sum, EMap(e, ELambda(arg, ONE)).with_type(TBag(INT))).with_type(INT), "<=", ONE).with_type(BOOL)

def EDeepEq(e1, e2):
    return EBinOp(e1, "===", e2).with_type(BOOL)

def EDeepIn(e1, e2):
    from cozy.syntax_tools import free_vars, fresh_var
    arg = fresh_var(e1.type, omit=free_vars(e1))
    return EUnaryOp(UOp.Any,
        EMap(e2, ELambda(arg,
            EDeepEq(arg, e1))).with_type(BOOL_BAG)).with_type(BOOL)

def ECountIn(e, collection):
    """Count the number of times e occurs in the collection"""
    from cozy.syntax_tools import free_vars, fresh_var
    assert e.type == collection.type.elem_type
    arg = fresh_var(e.type, omit=free_vars(e))
    return EUnaryOp(UOp.Length, EFilter(collection, ELambda(arg, EEq(arg, e))).with_type(collection.type)).with_type(INT)

def EArgDistinct(bag, key):
    from cozy.syntax_tools import mk_lambda
    b = EVar(fresh_name())
    distinct_keys = EUnaryOp(UOp.Distinct, EMap(b, key))
    res = EMap(distinct_keys,
        mk_lambda(None, lambda x:
            EUnaryOp(UOp.The, EFilter(b, mk_lambda(None, lambda y:
                EEq(x, key.apply_to(y)))))))
    return ELet(bag, ELambda(b, res))

def EForall(e, p):
    from cozy.syntax_tools import mk_lambda
    return EUnaryOp(UOp.All, EMap(e, mk_lambda(e.type.elem_type, p)).with_type(type(e.type)(BOOL))).with_type(BOOL)

def EDisjoint(xs, ys):
    return EForall(xs, lambda x:
        ENot(EIn(x, ys)))

# Misc
SWhile   = declare_case(Stm, "SWhile",  ["e", "body"])
SSwap    = declare_case(Stm, "SSwap",   ["lval1", "lval2"])
SSwitch  = declare_case(Stm, "SSwitch", ["e", "cases", "default"])
SReturn  = declare_case(Stm, "SReturn", ["e"])

# Fake go-to
SEscapableBlock = declare_case(Stm, "SEscapableBlock", ["label", "body"])
SEscapeBlock    = declare_case(Stm, "SEscapeBlock", ["label"])

# Bag transformations
EFilter  = declare_case(Exp, "EFilter",  ["e", "predicate"])
EMap     = declare_case(Exp, "EMap",     ["e", "transform_function"])
EFlatMap = declare_case(Exp, "EFlatMap", ["e", "transform_function"])

# List transformations
EDropFront = declare_case(Exp, "EDropFront", ["e"])
EDropBack  = declare_case(Exp, "EDropBack",  ["e"])

# Arrays
TArray = declare_case(Type, "TArray", ["elem_type"])
EArrayLen = declare_case(Exp, "EArrayLen", ["e"])
EArrayGet = declare_case(Exp, "EArrayGet", ["a", "i"])
EArrayIndexOf = declare_case(Exp, "EArrayIndexOf", ["a", "x"])
SArrayAlloc = declare_case(Stm, "SArrayAlloc", ["a", "capacity"])
SArrayReAlloc = declare_case(Stm, "SArrayReAlloc", ["a", "new_capacity"])
SEnsureCapacity = declare_case(Stm, "SEnsureCapacity", ["a", "capacity"])

# Maps
EEmptyMap  = declare_case(Exp, "EEmptyMap")
EMakeMap2  = declare_case(Exp, "EMakeMap2", ["e", "value_function"])
EMapGet    = declare_case(Exp, "EMapGet", ["map", "key"])
EHasKey    = declare_case(Exp, "EHasKey", ["map", "key"])
EMapKeys   = declare_case(Exp, "EMapKeys", ["e"])
SMapPut    = declare_case(Stm, "SMapPut", ["map", "key", "value"])
SMapDel    = declare_case(Stm, "SMapDel", ["map", "key"])
SMapUpdate = declare_case(Stm, "SMapUpdate", ["map", "key", "val_var", "change"]) # val_var is EVar
