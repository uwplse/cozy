"""Typechecking for Cozy specifications.

Important functions:
 - typecheck: find type errors in a specification and add type annotations
 - retypecheck: add or update type annotations to an internally-produced
   syntax tree
"""

from cozy.common import Visitor, OrderedSet
from cozy import syntax
from cozy import target_syntax
from cozy.syntax_tools import pprint, all_exps, free_vars

from cozy.syntax import BOOL, INT, LONG, FLOAT, STRING
from cozy.structures import extension_handler
from cozy.structures.arrays import TArray

def typecheck(
        ast,
        env : {str : syntax.Type} = None,
        fenv : {str : ([syntax.Type], syntax.Type)} = None):
    """Typecheck a syntax tree.

    This procedure attaches a .type attribute to every expression, and returns
    a list of type errors (or an empty list if everything typechecks properly).
    """
    typechecker = Typechecker(env or (), fenv or ())
    typechecker.visit(ast)
    return typechecker.errors

def retypecheck(exp, env : {str : syntax.Type} = None, fenv = None):
    """Add or fix the .type annotations on the given tree.

    Returns True or False to indicate success or failure.  If it fails, it
    prints type errors to stdout.

    Unlike `typecheck`, this procedure attempts to guess the types of variables
    and functions in the expression using their .type annotations.  The `env`
    dictionary overrides these guesses and forces variables to be annotated with
    a particular type.
    """
    if env is None:
        env = { v.id:v.type for v in free_vars(exp) }
    if fenv is not None:
        fenv = { f : (tuple(ty.arg_types), ty.ret_type) for f, ty in fenv.items() }
    else:
        fenv = { }
    for e in all_exps(exp):
        if isinstance(e, syntax.EEnumEntry):
            env[e.name] = e.type
        if isinstance(e, syntax.ECall):
            if e.func not in fenv:
                fenv[e.func] = (tuple(arg.type for arg in e.args), e.type)
    errs = typecheck(exp, env=env, fenv=fenv)
    if errs:
        print("errors")
        for e in errs:
            print(" --> {}".format(e))
    return not errs

DEFAULT_TYPE = object()

def is_numeric(t):
    return t in (INT, LONG, FLOAT)

_NON_NUMERIC_SCALAR_TYPES = set((
    syntax.TBool,
    syntax.TString,
    syntax.TNative,
    syntax.THandle,
    syntax.TEnum))

def is_scalar(t : syntax.Type):
    """Are values of type `t` storable in a constant number of bytes?"""
    if is_numeric(t):
        return True
    if type(t) in _NON_NUMERIC_SCALAR_TYPES:
        return True
    if isinstance(t, syntax.TTuple):
        return all(is_scalar(tt) for tt in t.ts)
    if isinstance(t, syntax.TRecord):
        return all(is_scalar(tt) for (f, tt) in t.fields)
    return False

def is_ordered(t : syntax.Type):
    return is_numeric(t) or isinstance(t, syntax.TNative)

def equality_implies_deep_equality(t : syntax.Type):
    """For values of type `t`, does "==" always behave the same as "==="?"""
    if isinstance(t, syntax.THandle):
        return False
    if is_numeric(t):
        return True
    if type(t) in _NON_NUMERIC_SCALAR_TYPES:
        return True
    if isinstance(t, syntax.TTuple):
        return all(equality_implies_deep_equality(tt) for tt in t.ts)
    if isinstance(t, syntax.TRecord):
        return all(equality_implies_deep_equality(tt) for (f, tt) in t.fields)
    if isinstance(t, syntax.TList):
        return equality_implies_deep_equality(t.elem_type)
    return False

COLLECTION_TYPES = (syntax.TBag, syntax.TSet, syntax.TList, TArray)
def is_collection(t):
    return any(isinstance(t, ct) for ct in COLLECTION_TYPES)

def to_abstract(t):
    if isinstance(t, syntax.TBag):
        return syntax.TBag(t.elem_type)
    if isinstance(t, syntax.TSet):
        return syntax.TSet(t.elem_type)
    if isinstance(t, syntax.TList):
        return syntax.TList(t.elem_type)
    return t

class Typechecker(Visitor):

    def __init__(self, env, fenv=()):
        self.tenv = {
            "Int":    INT,
            "Bound":  INT, # TODO?
            "Float":  FLOAT,
            "Long":   LONG,
            "Bool":   BOOL,
            "String": STRING }

        self.env = dict(env)
        self.fenv = dict(fenv)
        self.queries = dict()
        self.oldenv = []
        self.errors = []

    def push_scope(self):
        self.oldenv.append(self.env)
        self.env = dict(self.env)

    def pop_scope(self):
        self.env = self.oldenv[-1]
        del self.oldenv[-1]

    def scope(self):
        this = self
        class Scope(object):
            def __enter__(self, *args):
                this.push_scope()
            def __exit__(self, *args):
                this.pop_scope()
        return Scope()

    def visit_Spec(self, spec):
        for name, t in spec.types:
            self.tenv[name] = self.visit(t)
        spec.types = [(name, self.tenv[name]) for (name, t) in spec.types]
        spec.extern_funcs = [self.visit(f) for f in spec.extern_funcs]
        for name, t in spec.statevars:
            self.env[name] = self.visit(t)
        spec.statevars = [(name, self.env[name]) for (name, t) in spec.statevars]
        for op in spec.methods:
            self.visit(op)
        for e in spec.assumptions:
            self.visit(e)
            self.ensure_type(e, BOOL)

    def visit_ExternFunc(self, f):
        f = syntax.ExternFunc(
            f.name,
            [(arg_name, self.visit(arg_type)) for (arg_name, arg_type) in f.args],
            self.visit(f.out_type),
            f.body_string)
        self.fenv[f.name] = (tuple(t for (a, t) in f.args), f.out_type)
        return f

    def report_err(self, source, msg):
        self.errors.append("At {}: {}".format(pprint(source), msg))

    def visit_TEnum(self, t):
        for x in t.cases:
            self.env[x] = t
        return t

    def visit_TNamed(self, t):
        if t.id in self.tenv:
            return self.tenv[t.id]
        self.report_err(t, "unknown type {}".format(t.id))
        return t

    def visit_TApp(self, t):
        if t.type_name == "Set":
            return syntax.TSet(self.visit(t.args))
        elif t.type_name == "Bag":
            return syntax.TBag(self.visit(t.args))
        elif t.type_name == "List":
            return syntax.TList(self.visit(t.args))
        else:
            self.report_err(t, "unknown type {}".format(t.type_name))
            return t

    def visit_TRecord(self, t):
        return syntax.TRecord(tuple((f, self.visit(ft)) for f, ft in t.fields))

    def visit_TTuple(self, t):
        return syntax.TTuple(tuple(self.visit(tt) for tt in t.ts))

    def visit_THandle(self, t):
        return syntax.THandle(t.statevar, self.visit(t.value_type))

    def visit_TBool(self, t):
        return t

    def visit_TString(self, t):
        return t

    def visit_TInt(self, t):
        return t

    def visit_TLong(self, t):
        return t

    def visit_TFloat(self, t):
        return t

    def visit_TNative(self, t):
        return t

    def visit_TBag(self, t):
        return type(t)(self.visit(t.elem_type))

    def visit_TSet(self, t):
        return type(t)(self.visit(t.elem_type))

    def visit_TList(self, t):
        return type(t)(self.visit(t.elem_type))

    def visit_TMap(self, t):
        return type(t)(self.visit(t.k), self.visit(t.v))

    def types_equivalent(self, t1, t2):
        if isinstance(t1, syntax.TMap) and isinstance(t2, syntax.TMap):
            return self.types_equivalent(t1.k, t2.k) and self.types_equivalent(t1.v, t2.v)
        elif isinstance(t1, syntax.TBag) and isinstance(t2, syntax.TBag):
            return self.types_equivalent(t1.elem_type, t2.elem_type)
        elif isinstance(t1, syntax.TSet) and isinstance(t2, syntax.TSet):
            return self.types_equivalent(t1.elem_type, t2.elem_type)
        else:
            return t1 == t2

    def ensure_type(self, e, t, msg="expression has type {} instead of {}"):
        if not hasattr(e, "type"):
            self.visit(e)
        if t is not DEFAULT_TYPE and e.type is not DEFAULT_TYPE and not self.types_equivalent(e.type, t):
            self.report_err(e, msg.format(pprint(e.type), pprint(t)))

    def check_assignment(self, node, ltype, rtype):
        if ltype == rtype or ltype is DEFAULT_TYPE or rtype is DEFAULT_TYPE:
            return
        if is_collection(ltype) and is_collection(rtype):
            return
        self.report_err(node, "cannot assign {} to a {}".format(pprint(rtype), pprint(ltype)))

    def ensure_numeric(self, e):
        if e.type is DEFAULT_TYPE:
            return
        if not is_numeric(e.type):
            self.report_err(e, "expression has non-numeric type {}".format(e.type))

    def lub(self, src, t1, t2, explanation):
        if t1 == t2:
            return t1
        if is_numeric(t1) and is_numeric(t2):
            return self.numeric_lub(src, t1, t2)
        if isinstance(t1, syntax.TList) and isinstance(t2, syntax.TList) and t1.elem_type == t2.elem_type:
            return syntax.TList(t1.elem_type)
        if is_collection(t1) and is_collection(t2) and t1.elem_type == t2.elem_type:
            return syntax.TBag(t1.elem_type)
        if t1 is DEFAULT_TYPE:
            return t2
        if t2 is DEFAULT_TYPE:
            return t1
        self.report_err(src, "cannot unify types {} and {} ({})".format(pprint(t1), pprint(t2), explanation))
        return DEFAULT_TYPE

    def numeric_lub(self, src, t1, t2):
        if t1 == LONG or t2 == LONG:
            return LONG
        if t1 == INT and t2 == INT:
            return INT
        if t1 == FLOAT and t2 == FLOAT:
            return FLOAT
        self.report_err(src, "cannot unify types {} and {}".format(pprint(t1), pprint(t2)))
        return DEFAULT_TYPE

    def get_collection_type(self, e):
        """if e has a collection type, e.g. List<Int>, this returns the inner type, e.g. Int"""
        if e.type is DEFAULT_TYPE:           return DEFAULT_TYPE
        if isinstance(e.type, syntax.TBag):  return e.type.elem_type
        if isinstance(e.type, syntax.TSet):  return e.type.elem_type
        if isinstance(e.type, syntax.TList): return e.type.elem_type
        self.report_err(e, "expression has non-collection type {}".format(e.type))
        return DEFAULT_TYPE

    def get_map_type(self, e):
        if e.type is DEFAULT_TYPE: return DEFAULT_TYPE
        if isinstance(e.type, syntax.TMap):
            return e.type.k, e.type.v
        self.report_err(e, "expression has non-map type {}".format(e.type))
        return DEFAULT_TYPE, DEFAULT_TYPE

    def get_handle_type(self, e):
        if e.type is DEFAULT_TYPE: return DEFAULT_TYPE
        if isinstance(e.type, syntax.THandle):
            return e.type.value_type
        self.report_err(e, "expression has non-handle type {}".format(e.type))
        return DEFAULT_TYPE

    def visit_ELet(self, e):
        self.visit(e.e)
        e.body_function.arg.type = e.e.type
        self.visit(e.body_function)
        e.type = e.body_function.body.type

    def visit_EUnaryOp(self, e):
        self.visit(e.e)
        if e.op == syntax.UOp.Sum:
            tt = self.get_collection_type(e.e)
            if is_numeric(tt) or tt is DEFAULT_TYPE:
                e.type = tt
            else:
                self.report_err(e, "cannot sum {}".format(e.e.type))
                e.type = DEFAULT_TYPE
        elif e.op in [syntax.UOp.AreUnique, syntax.UOp.Empty, syntax.UOp.Exists]:
            self.get_collection_type(e.e)
            e.type = BOOL
        elif e.op == syntax.UOp.Distinct:
            t = self.get_collection_type(e.e)
            e.type = to_abstract(e.e.type)
        elif e.op == syntax.UOp.The:
            e.type = self.get_collection_type(e.e)
        elif e.op in [syntax.UOp.Any, syntax.UOp.All]:
            t = self.get_collection_type(e.e)
            self.lub(e, t, BOOL, "{op} must be over collection of bools".format(op=e.op))
            e.type = BOOL
        elif e.op == syntax.UOp.Length:
            self.get_collection_type(e.e)
            e.type = INT
        elif e.op == syntax.UOp.Not:
            self.ensure_type(e.e, BOOL)
            e.type = BOOL
        elif e.op == syntax.UOp.Reversed:
            if isinstance(e.e.type, syntax.TList):
                e.type = e.e.type
            else:
                self.report_err(e, "cannot reverse {}".format(e.e.type))
                e.type = DEFAULT_TYPE
        elif e.op == "-":
            self.ensure_numeric(e.e)
            e.type = e.e.type
        else:
            raise NotImplementedError(e.op)

    def visit_EArgMin(self, e):
        self.visit(e.e)
        e.key_function.arg.type = self.get_collection_type(e.e)
        self.visit(e.key_function)
        e.type = e.key_function.arg.type
        # todo: ensure sortable (e.key_function.arg.type)

    def visit_EArgMax(self, e):
        self.visit(e.e)
        e.key_function.arg.type = self.get_collection_type(e.e)
        self.visit(e.key_function)
        e.type = e.key_function.arg.type
        # todo: ensure sortable (e.key_function.arg.type)

    def visit_EBool(self, e):
        e.type = BOOL

    def visit_ENum(self, e):
        if not hasattr(e, "type"):
            self.report_err(e, "Not sure what the type of numeric literal {} is!".format(e.val))
            e.type = DEFAULT_TYPE

    def visit_EStr(self, e):
        e.type = STRING

    def visit_ENull(self, e):
        if not hasattr(e, "type"):
            self.report_err(e, "not sure what type this NULL should have")
            e.type = DEFAULT_TYPE

    def visit_ECond(self, e):
        self.visit(e.cond)
        self.visit(e.then_branch)
        self.visit(e.else_branch)
        self.ensure_type(e.cond, BOOL)
        e.type = self.lub(e, e.else_branch.type, e.then_branch.type,
            "cases in ternary expression must have the same type")

    def visit_ELambda(self, e):
        with self.scope():
            self.env[e.arg.id] = e.arg.type
            self.visit(e.body)

    def visit_EBinOp(self, e):
        self.visit(e.e1)
        self.visit(e.e2)
        if e.op in ["==", "===", "!=", "<", "<=", ">", ">="]:
            self.lub(e, e.e1.type, e.e2.type, "due to comparison")
            e.type = BOOL
        elif e.op in [syntax.BOp.And, syntax.BOp.Or, "=>"]:
            self.ensure_type(e.e1, BOOL)
            self.ensure_type(e.e2, BOOL)
            e.type = BOOL
        elif e.op == syntax.BOp.In:
            t = self.get_collection_type(e.e2)
            self.ensure_type(e.e1, t)
            e.type = BOOL
        elif e.op in ["+", "-"]:
            if is_numeric(e.e1.type):
                self.ensure_numeric(e.e2)
                e.type = self.numeric_lub(e, e.e1.type, e.e2.type)
            else:
                t1 = self.get_collection_type(e.e1)
                t2 = self.get_collection_type(e.e2)
                if t1 != t2:
                    self.report_err(e, "cannot {!r} {} and {}".format(e.op, pprint(e.e1.type), pprint(e.e2.type)))
                e.type = to_abstract(e.e1.type)
        elif e.op in ["*"]:
            if is_numeric(e.e1.type):
                e.type = self.numeric_lub(e, e.e1.type, e.e2.type)
                if not isinstance(e.e1, syntax.ENum) and not isinstance(e.e2, syntax.ENum):
                    self.report_err(e, "multiplication is only legal when one operand is a constant")
            else:
                e.type = DEFAULT_TYPE
                self.report_err(e, "cannot multiply {} and {}".format(pprint(e.e1.type), pprint(e.e2.type)))
        elif e.op == "/":
            e.type = FLOAT
            if not (e.e1.type is DEFAULT_TYPE or e.e1.type == FLOAT):
                self.report_err(e, "division is only legal on floats; left-hand side {} has type {}".format(pprint(e.e1), pprint(e.e1.type)))
            if not (e.e2.type is DEFAULT_TYPE or e.e2.type == FLOAT):
                self.report_err(e, "division is only legal on floats; right-hand side {} has type {}".format(pprint(e.e2), pprint(e.e2.type)))
            self.report_err(e,
                "Division is currently unsupported since it is a partial function (x/0 is undefined)."
                + "  See https://github.com/CozySynthesizer/cozy/issues/19 for more information.")
        else:
            raise NotImplementedError(e.op)

    def visit_EFlatMap(self, e):
        self.visit(e.e)
        t1 = self.get_collection_type(e.e)
        self.visit(e.transform_function)
        self.ensure_type(e.transform_function.arg, t1)
        t2 = self.get_collection_type(e.transform_function.body)
        e.type = e.transform_function.body.type

    def visit_ECall(self, e):
        fname = e.func
        f = self.fenv.get(fname) or self.queries.get(fname)
        if f is None:
            self.report_err(e, "unknown function {}".format(repr(fname)))
        if isinstance(f, syntax.Query):
            f = (tuple(t for (a, t) in f.args), f.ret.type)

        for a in e.args:
            self.visit(a)

        if f is not None:
            arg_types, out_type = f
            if len(arg_types) != len(e.args):
                self.report_err(e, "wrong number of arguments to {}".format(repr(fname)))
            i = 1
            for arg_type, arg_val in zip(arg_types, e.args):
                self.ensure_type(arg_val, arg_type, "argument {} to {} has type {{}} instead of {{}}".format(i, fname))
                i += 1
            e.type = out_type
        else:
            e.type = DEFAULT_TYPE

    def visit_EEmptyList(self, e):
        if not hasattr(e, "type"):
            self.report_err(e, "unable to infer type for empty collection")
        else:
            self.get_collection_type(e)

    def visit_ESingleton(self, e):
        self.visit(e.e)
        e.type = syntax.TList(e.e.type)

    def visit_EListGet(self, e):
        self.visit(e.e)
        if isinstance(e.e.type, syntax.TList):
            e.type = e.e.type.elem_type
        else:
            e.type = DEFAULT_TYPE
            if e.e.type is not DEFAULT_TYPE:
                self.report_err(e, "cannot get element from non-list")
        self.visit(e.index)
        self.ensure_type(e.index, INT, "list index must be an Int")

    def visit_EListSlice(self, e):
        self.visit(e.e)
        if isinstance(e.e.type, syntax.TList):
            e.type = e.e.type
        else:
            e.type = DEFAULT_TYPE
            if e.e.type is not DEFAULT_TYPE:
                self.report_err(e, "cannot get element from non-list")
        self.visit(e.start)
        self.ensure_type(e.start, INT, "slice start must be an Int")
        self.visit(e.end)
        self.ensure_type(e.end, INT, "slice end must be an Int")

    def visit_EListComprehension(self, e):
        collection_types = OrderedSet()
        with self.scope():
            for clause in e.clauses:
                self.visit(clause)
                if isinstance(clause, syntax.CPull) and clause.e.type is not DEFAULT_TYPE:
                    collection_types.add(clause.e.type)
            self.visit(e.e)

        if all(isinstance(t, syntax.TList) for t in collection_types):
            e.type = syntax.TList(e.e.type)
        else:
            e.type = syntax.TBag(e.e.type)

    def visit_EMakeRecord(self, e):
        fields = []
        for f, val in e.fields:
            self.visit(val)
            fields.append((f, val.type))
        e.type = syntax.TRecord(tuple(fields))

    def visit_CPull(self, c):
        self.visit(c.e)
        t = self.get_collection_type(c.e)
        self.env[c.id] = t

    def visit_CCond(self, c):
        self.ensure_type(c.e, BOOL)

    def visit_EGetField(self, e):
        self.visit(e.e)
        if e.e.type is DEFAULT_TYPE:
            e.type = DEFAULT_TYPE
            return
        if isinstance(e.e.type, syntax.TRecord):
            fields = dict(e.e.type.fields)
            if e.field_name in fields:
                e.type = fields[e.field_name]
            else:
                self.report_err(e, "no field {} on type {}".format(e.field_name, e.e.type))
                e.type = DEFAULT_TYPE
        elif isinstance(e.e.type, syntax.THandle):
            if e.field_name == "val":
                e.type = e.e.type.value_type
            else:
                self.report_err(e, "no field {} on type {}".format(e.field_name, e.e.type))
                e.type = DEFAULT_TYPE
        else:
            self.report_err(e, "cannot get field {} from non-record {}".format(e.field_name, e.e.type))
            e.type = DEFAULT_TYPE

    def visit_EVar(self, e):
        if e.id in self.env:
            e.type = self.env[e.id]
        else:
            self.report_err(e, "no var {} in scope".format(e.id))
            e.type = DEFAULT_TYPE

    def visit_EEnumEntry(self, e):
        if e.name in self.env:
            e.type = self.env[e.name]
        else:
            self.report_err(e, "no enum entry {} in scope".format(e.name))
            e.type = DEFAULT_TYPE

    def visit_ENative(self, e):
        self.visit(e.e)
        self.ensure_type(e.e, INT)
        if not hasattr(e, "type"):
            self.report_err(e, "not enough information to construct type for ENative expression")
            e.type = DEFAULT_TYPE

    def visit_EHandle(self, e):
        self.visit(e.addr)
        self.ensure_type(e.addr, INT)
        self.visit(e.value)
        if hasattr(e, "type"):
            self.ensure_type(e.value, e.type.value_type)
        else:
            self.report_err(e, "not enough information to construct type for EHandle expression")
            e.type = DEFAULT_TYPE

    def visit_ETuple(self, e):
        for ee in e.es:
            self.visit(ee)
        e.type = syntax.TTuple(tuple(ee.type for ee in e.es))

    def visit_ETupleGet(self, e):
        self.visit(e.e)
        t = e.e.type
        if isinstance(t, syntax.TTuple):
            if e.index >= 0 and e.index < len(t.ts):
                e.type = t.ts[e.index]
            else:
                self.report_err(e, "cannot get element {} from tuple of size {}".format(e.index, len(t.ts)))
                e.type = DEFAULT_TYPE
        elif t is DEFAULT_TYPE:
            e.type = DEFAULT_TYPE
        else:
            self.report_err(e, "cannot get element from non-tuple {}".format(pprint(t)))
            e.type = DEFAULT_TYPE

    def visit_EMap(self, e):
        self.visit(e.e)
        elem_type = self.get_collection_type(e.e)
        e.transform_function.arg.type = elem_type
        self.visit(e.transform_function)
        if isinstance(e.e.type, syntax.TSet):
            # Sets might not have distinct elements after the map transform.
            # Consider e.g. `map {\x -> 1} my_set`.
            e.type = syntax.TBag(e.transform_function.body.type)
        elif is_collection(e.e.type):
            e.type = type(to_abstract(e.e.type))(e.transform_function.body.type)
        elif e.e.type is DEFAULT_TYPE:
            e.type = DEFAULT_TYPE
        else:
            self.report_err(e, "cannot map over non-collection {}".format(pprint(e.e.type)))
            e.type = DEFAULT_TYPE

    def visit_EFilter(self, e):
        self.visit(e.e)
        elem_type = self.get_collection_type(e.e)
        e.predicate.arg.type = elem_type
        self.visit(e.predicate)
        self.ensure_type(e.predicate.body, BOOL)
        e.type = to_abstract(e.e.type)

    def visit_EMakeMap2(self, e):
        self.visit(e.e)
        t = self.get_collection_type(e.e)
        e.value_function.arg.type = t
        self.visit(e.value_function)
        e.type = syntax.TMap(t, e.value_function.body.type)

    def visit_EMapKeys(self, e):
        self.visit(e.e)
        k, v = self.get_map_type(e.e)
        e.type = syntax.TBag(k)

    def visit_EHasKey(self, e):
        self.visit(e.map)
        self.visit(e.key)
        if isinstance(e.map.type, syntax.TMap):
            self.ensure_type(e.key, e.map.type.k)
        else:
            self.report_err(e, "{} is not a map".format(e.map))
        e.type = BOOL

    def visit_EMapGet(self, e):
        self.visit(e.map)
        self.visit(e.key)
        if not isinstance(e.map.type, syntax.TMap):
            self.report_err(e, "{} is not a map".format(e.map))
            e.type = DEFAULT_TYPE
            return
        self.ensure_type(e.key, e.map.type.k)
        e.type = e.map.type.v

    def visit_EStateVar(self, e):
        self.visit(e.e)
        e.type = e.e.type

    def report(self, e, err):
        self.report_err(e, err)
        e.type = DEFAULT_TYPE

    def visit_Exp(self, e):
        h = extension_handler(type(e))
        if h is not None:
            h.typecheck(e, self.visit, self.report)

    def visit_SMapUpdate(self, s):
        self.visit(s.map)
        if not isinstance(s.map.type, syntax.TMap):
            self.report_err(s, "{} is not a map".format(s.map))
        self.visit(s.key)
        self.ensure_type(s.key, s.map.type.k)
        with self.scope():
            self.env[s.val_var.id] = s.map.type.v
            s.val_var.type = s.map.type.v
            self.visit(s.change)

    def visit_SMapPut(self, s):
        self.visit(s.map)
        self.visit(s.key)
        self.visit(s.value)
        k, v = self.get_map_type(s.map)
        self.ensure_type(s.key, k)
        self.check_assignment(s, v, s.value.type)

    def visit_SMapDel(self, s):
        self.visit(s.map)
        self.visit(s.key)
        k, v = self.get_map_type(s.map)
        self.ensure_type(s.key, k)

    def visit_Op(self, op):
        op.args = [(name, self.visit(t)) for (name, t) in op.args]
        with self.scope():
            for name, t in op.args:
                self.env[name] = self.visit(t)
            for e in op.assumptions:
                self.visit(e)
                self.ensure_type(e, BOOL)
            self.visit(op.body)

    def visit_Query(self, q):
        q.args = [(name, self.visit(t)) for (name, t) in q.args]
        with self.scope():
            for name, t in q.args:
                self.env[name] = self.visit(t)
            for e in q.assumptions:
                self.visit(e)
                self.ensure_type(e, BOOL)
            self.visit(q.ret)
        q.out_type = q.ret.type
        self.queries[q.name] = q

    def visit_SCall(self, s):
        self.visit(s.target)
        for a in s.args:
            self.visit(a)
        if s.func == "add":
            elem_type = self.get_collection_type(s.target)
            if len(s.args) != 1:
                self.report_err(s, "add takes exactly 1 argument")
            if len(s.args) > 0:
                self.ensure_type(s.args[0], elem_type)
        elif s.func in ("add_front", "add_back"):
            if isinstance(s.target.type, syntax.TList):
                elem_type = s.target.type.elem_type
                if len(s.args) != 1:
                    self.report_err(s, "{f} takes exactly 1 argument".format(f=s.func))
                if len(s.args) > 0:
                    self.ensure_type(s.args[0], elem_type)
            else:
                if s.target.type is not DEFAULT_TYPE:
                    self.report_err(s, "target must be a list")
        elif s.func in ("remove_front", "remove_back"):
            if isinstance(s.target.type, syntax.TList):
                if len(s.args) != 0:
                    self.report_err(s, "{f} does not take arguments".format(f=s.func))
            else:
                if s.target.type is not DEFAULT_TYPE:
                    self.report_err(s, "target must be a list")
        elif s.func == "remove":
            elem_type = self.get_collection_type(s.target)
            if len(s.args) != 1:
                self.report_err(s, "remove takes exactly 1 argument")
            if len(s.args) > 0:
                self.ensure_type(s.args[0], elem_type)
        elif s.func == "remove_all":
            elem_type = self.get_collection_type(s.target)
            if len(s.args) != 1:
                self.report_err(s, "remove_all takes exactly 1 argument")
            if len(s.args) > 0:
                tt = self.get_collection_type(s.args[0])
                self.lub(s.args[0], elem_type, tt, "call to remove_all")
        else:
            self.report_err(s, "unknown function {}".format(s.func))

    def visit_SSeq(self, s):
        self.visit(s.s1)
        self.visit(s.s2)

    def visit_SIf(self, s):
        self.visit(s.cond)
        self.ensure_type(s.cond, syntax.TBool())
        with self.scope():
            self.visit(s.then_branch)
        with self.scope():
            self.visit(s.else_branch)

    def visit_SNoOp(self, s):
        pass

    def visit_SAssign(self, s):
        self.visit(s.lhs)
        self.visit(s.rhs)
        self.check_assignment(s, s.lhs.type, s.rhs.type)

    def visit_SForEach(self, s):
        assert isinstance(s.loop_var, syntax.EVar)
        with self.scope():
            self.visit(s.iter)
            t = self.get_collection_type(s.iter)
            self.env[s.loop_var.id] = t
            self.visit(s.body)

    def visit_SDecl(self, s):
        self.visit(s.val)
        s.var.type = s.val.type
        self.env[s.var.id] = s.val.type

    def visit(self, x):
        res = super().visit(x)
        should_have_type = isinstance(x, syntax.Exp) and not isinstance(x, target_syntax.ELambda)
        if should_have_type and (not hasattr(x, "type") or x.type is None):
            raise Exception(x)
        return res
