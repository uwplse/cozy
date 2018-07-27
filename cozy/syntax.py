"""Abstract syntax for Cozy specifications."""

from enum import Enum

from cozy.common import ADT, declare_case, typechecked, partition, make_random_access

Spec                = declare_case(ADT, "Spec", ["name", "types", "extern_funcs", "statevars", "assumptions", "methods", "header", "footer", "docstring"])
ExternFunc          = declare_case(ADT, "ExternFunc", ["name", "args", "out_type", "body_string"])

class Visibility(Enum):
    """Visibilities for queries in Cozy specifications."""
    Public   = "public"   # usable by clients
    Private  = "private"  # private helper used by other methods
    Internal = "internal" # helper added by Cozy, not by a human programmer

class Method(ADT): pass
Op                  = declare_case(Method, "Op",    ["name", "args", "assumptions", "body", "docstring"])
Query               = declare_case(Method, "Query", ["name", "visibility", "args", "assumptions", "ret", "docstring"])

class Type(ADT): pass
TInt                = declare_case(Type, "TInt")
TLong               = declare_case(Type, "TLong")
TFloat              = declare_case(Type, "TFloat")
TBool               = declare_case(Type, "TBool")
TString             = declare_case(Type, "TString")
TNative             = declare_case(Type, "TNative", ["name"])
THandle             = declare_case(Type, "THandle", ["statevar", "value_type"])
TBag                = declare_case(Type, "TBag",    ["elem_type"])
TSet                = declare_case(Type, "TSet",    ["elem_type"])
TList               = declare_case(Type, "TList",   ["elem_type"])
TMap                = declare_case(Type, "TMap",    ["k", "v"])
TNamed              = declare_case(Type, "TNamed",  ["id"])
TRecord             = declare_case(Type, "TRecord", ["fields"])
TApp                = declare_case(Type, "TApp",    ["elem_type", "args"])
TEnum               = declare_case(Type, "TEnum",   ["cases"])
TTuple              = declare_case(Type, "TTuple",  ["ts"])

# Unary operators
class UOp(object):
    Sum       = "sum"
    Not       = "not"
    Distinct  = "distinct"
    AreUnique = "unique"
    All       = "all"
    Any       = "any"
    Exists    = "exists"
    Length    = "len"
    Empty     = "empty"
    The       = "the"
    Reversed  = "reversed"

UOps = (UOp.Sum,
        UOp.Not,
        UOp.Distinct,
        UOp.AreUnique,
        UOp.All,
        UOp.Any,
        UOp.Exists,
        UOp.Length,
        UOp.Empty,
        UOp.The,
        UOp.Reversed)

# Binary operators
class BOp(object):
    And = "and"
    Or  = "or"
    In  = "in"

BOps = (BOp.And,
        BOp.Or,
        BOp.In)

class Exp(ADT):
    def with_type(self, t):
        self.type = t
        return self
    def __repr__(self):
        s = super().__repr__()
        if hasattr(self, "type"):
            s += ".with_type({})".format(repr(self.type))
        return s

EVar                = declare_case(Exp, "EVar",               ["id"])
EBool               = declare_case(Exp, "EBool",              ["val"])
ENum                = declare_case(Exp, "ENum",               ["val"])
EStr                = declare_case(Exp, "EStr",               ["val"])
ENative             = declare_case(Exp, "ENative",            ["e"])
EEnumEntry          = declare_case(Exp, "EEnumEntry",         ["name"])
ENull               = declare_case(Exp, "ENull")
ECond               = declare_case(Exp, "ECond",              ["cond", "then_branch", "else_branch"])
EBinOp              = declare_case(Exp, "EBinOp",             ["e1", "op", "e2"])
EUnaryOp            = declare_case(Exp, "EUnaryOp",           ["op", "e"])
EArgMin             = declare_case(Exp, "EArgMin",            ["e", "key_function"])
EArgMax             = declare_case(Exp, "EArgMax",            ["e", "key_function"])
EHandle             = declare_case(Exp, "EHandle",            ["addr", "value"])
EGetField           = declare_case(Exp, "EGetField",          ["e", "field_name"])
EMakeRecord         = declare_case(Exp, "EMakeRecord",        ["fields"])
EListGet            = declare_case(Exp, "EListGet",           ["e", "index"])
EListSlice          = declare_case(Exp, "EListSlice",         ["e", "start", "end"])
EListComprehension  = declare_case(Exp, "EListComprehension", ["e", "clauses"])
EEmptyList          = declare_case(Exp, "EEmptyList")
ESingleton          = declare_case(Exp, "ESingleton",         ["e"])
ECall               = declare_case(Exp, "ECall",              ["func", "args"])
ETuple              = declare_case(Exp, "ETuple",             ["es"])
ETupleGet           = declare_case(Exp, "ETupleGet",          ["e", "index"])
ELet                = declare_case(Exp, "ELet",               ["e", "body_function"])

# Lambdas
TFunc = declare_case(Type, "TFunc", ["arg_types", "ret_type"])
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

class ComprehensionClause(ADT): pass
CPull               = declare_case(ComprehensionClause, "CPull", ["id", "e"])
CCond               = declare_case(ComprehensionClause, "CCond", ["e"])

class Stm(ADT): pass
SNoOp               = declare_case(Stm, "SNoOp")
SSeq                = declare_case(Stm, "SSeq",     ["s1", "s2"])
SCall               = declare_case(Stm, "SCall",    ["target", "func", "args"])
SAssign             = declare_case(Stm, "SAssign",  ["lhs", "rhs"])
SDecl               = declare_case(Stm, "SDecl",    ["var", "val"]) # EVar var
SForEach            = declare_case(Stm, "SForEach", ["loop_var", "iter", "body"]) # EVar id
SIf                 = declare_case(Stm, "SIf",      ["cond", "then_branch", "else_branch"])

# -----------------------------------------------------------------------------
# Various utilities

BOOL = TBool()
INT = TInt()
LONG = TLong()
FLOAT = TFloat()
STRING = TString()
BOOL_BAG = TBag(BOOL)
INT_BAG = TBag(INT)

ETRUE = EBool(True) .with_type(BOOL)
EFALSE = EBool(False).with_type(BOOL)
ZERO = ENum(0).with_type(INT)
ONE = ENum(1).with_type(INT)
TWO = ENum(2).with_type(INT)
NULL = ENull()

def build_balanced_tree(es, f, start=None, end=None):
    """Create a balanced syntax tree out of an associative binary operator.

    Many internal functions do not like deep, stick-shaped trees since those
    functions are recursive and Python has a small-ish maximum stack depth.

    Parameters:
        es    - a non-empty list of syntax trees
        f     - a function that takes two syntax trees and returns a new one
        start - if non-none, only use expressions in es[start:]
        end   - if non-none, only use expressions in es[:end]
    """
    if start is None:
        start = 0
    if end is None:
        end = len(es)
    n = end - start
    assert n > 0, "cannot create balanced tree out of empty list"
    if n == 1:
        return es[start]
    else:
        cut = start + (n // 2)
        return f(
            build_balanced_tree(es, f, start=start, end=cut),
            build_balanced_tree(es, f, start=cut, end=end))

def build_balanced_binop_tree(t : Type, op : BOp, es : [Exp]):
    """Create a balanced expression tree out of an associative binary operator.

    See build_balanced_tree for an explanation of why you would want this.

    Parameters:
        t     - the type of expressions in `es`
        op    - a binary operator
        es    - a non-empty list of expressions
    """
    es = make_random_access(es)
    return build_balanced_tree(es, lambda e1, e2: EBinOp(e1, op, e2).with_type(t))

def seq(stms):
    stms = [s for s in stms if not isinstance(s, SNoOp)]
    if not stms:
        return SNoOp()
    return build_balanced_tree(stms, SSeq)

def EAll(exps):
    exps = [ e for e in exps if e != ETRUE ]
    if any(e == EFALSE for e in exps):
        return EFALSE
    if not exps:
        return ETRUE
    return build_balanced_binop_tree(BOOL, BOp.And, exps)

def EAny(exps):
    exps = [ e for e in exps if e != EFALSE ]
    if any(e == ETRUE for e in exps):
        return ETRUE
    if not exps:
        return EFALSE
    return build_balanced_binop_tree(BOOL, BOp.Or, exps)

def ENot(e):
    if isinstance(e, EUnaryOp) and e.op == "not":
        return e.e
    return EUnaryOp("not", e).with_type(BOOL)

def EIsSubset(e1, e2):
    return EEmpty(EBinOp(e1, "-", e2).with_type(e1.type))

def EIsSingleton(e):
    return EEq(EUnaryOp(UOp.Length, e).with_type(INT), ONE)

def EEmpty(e):
    return EUnaryOp(UOp.Empty, e).with_type(BOOL)

def EExists(e):
    return EUnaryOp(UOp.Exists, e).with_type(BOOL)

def EEq(e1, e2):
    return EBinOp(e1, "==", e2).with_type(BOOL)

def EGt(e1, e2):
    return EBinOp(e1, ">", e2).with_type(BOOL)

def ELt(e1, e2):
    return EBinOp(e1, "<", e2).with_type(BOOL)

def EGe(e1, e2):
    return EBinOp(e1, ">=", e2).with_type(BOOL)

def ELe(e1, e2):
    return EBinOp(e1, "<=", e2).with_type(BOOL)

def EIn(e1, e2):
    return EBinOp(e1, BOp.In, e2).with_type(BOOL)

def EImplies(e1, e2):
    return EBinOp(e1, "=>", e2).with_type(BOOL)

def ELen(e):
    if isinstance(e, EEmptyList):
        return ZERO
    if isinstance(e, ESingleton):
        return ONE
    return EUnaryOp(UOp.Length, e).with_type(INT)

def ESum(es, base_case=ZERO):
    es = [e for e in es if e != base_case]
    if not es:
        return base_case
    nums, nonnums = partition(es, lambda e: isinstance(e, ENum))
    es = nonnums
    if nums:
        es.append(ENum(sum(n.val for n in nums)).with_type(base_case.type))
    return build_balanced_binop_tree(base_case.type, "+", es)

def EUnion(es, elem_type):
    return ESum(es, base_case=EEmptyList().with_type(TBag(elem_type)))

def EIntersect(xs, ys):
    a = EBinOp(xs, "-", ys).with_type(xs.type) # xs - (xs intersect ys)
    b = EBinOp(xs, "-", a).with_type(xs.type)  # xs intersect ys
    return b

def max_of(*es, type=None):
    if not es:
        if type is None:
            raise ValueError("need to supply `type=...` keyword argument for max_of to support an empty set of arguments")
        x = EVar("x").with_type(type)
        return EArgMax(EEmptyList().with_type(TBag(type)), ELambda(x, x)).with_type(type)
    if len(es) == 1:
        return es[0]
    type = es[0].type if type is None else type
    x = EVar("x").with_type(type)
    if type is None:
        raise ValueError("no type supplied")
    t_bag = TBag(type)
    parts = ESum([ESingleton(e).with_type(t_bag) for e in es], base_case=EEmptyList().with_type(t_bag))
    return EArgMax(parts, ELambda(x, x)).with_type(type)

def min_of(*es, type=None):
    if not es:
        if type is None:
            raise ValueError("need to supply `type=...` keyword argument for max_of to support an empty set of arguments")
        x = EVar("x").with_type(type)
        return EArgMin(EEmptyList().with_type(TBag(type)), ELambda(x, x)).with_type(type)
    if len(es) == 1:
        return es[0]
    type = es[0].type if type is None else type
    x = EVar("x").with_type(type)
    if type is None:
        raise ValueError("no type supplied")
    t_bag = TBag(type)
    parts = ESum([ESingleton(e).with_type(t_bag) for e in es], base_case=EEmptyList().with_type(t_bag))
    return EArgMin(parts, ELambda(x, x)).with_type(type)

def nth_func(t : TTuple, n : int) -> ELambda:
    """Returns a lambda expression that obtains the nth element of a tuple."""
    ## Hard-coded variable name is OK because no capturing or shadowing is possible.
    x = EVar("x").with_type(t)
    return ELambda(x, ETupleGet(x, n).with_type(t.ts[n]))
