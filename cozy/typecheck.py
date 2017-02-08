from cozy.common import Visitor
from cozy import syntax
from cozy import target_syntax
from cozy.syntax_tools import pprint

def typecheck(ast, env=None, handleize=True):
    """
    Typecheck the syntax tree.
    This procedure attaches a .type attribute to every expression, and returns
    a list of type errors (or an empty list if everything typechecks properly).
    """
    typechecker = Typechecker(env or (), handleize)
    typechecker.visit(ast)
    return typechecker.errors

def retypecheck(exp, env=None):
    from cozy.syntax_tools import free_vars
    if env is None:
        env = { v.id:v.type for v in free_vars(exp) }
    errs = typecheck(exp, env=env, handleize=False)
    if errs:
        print("errors")
        for e in errs:
            print(" --> {}".format(e))
    return not errs

BOOL = syntax.BOOL
INT = syntax.INT
LONG = syntax.LONG
STRING = syntax.STRING
DEFAULT_TYPE = object()

class Typechecker(Visitor):

    def __init__(self, env, handleize):
        self.tenv = {
            "Int": INT,
            "Bound": INT, # TODO?
            "Long": LONG,
            "Bool": BOOL,
            "String": STRING }

        self.env = dict(env)
        self.funcs = dict()
        self.queries = dict()
        self.should_handleize = handleize
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
            self.env[name] = self.handleize(self.visit(t), name)
        spec.statevars = [(name, self.env[name]) for (name, t) in spec.statevars]
        for e in spec.assumptions:
            self.visit(e)
            self.ensure_type(e, BOOL)
        for op in spec.methods:
            self.visit(op)

    def visit_ExternFunc(self, f):
        f = syntax.ExternFunc(
            f.name,
            [(arg_name, self.visit(arg_type)) for (arg_name, arg_type) in f.args],
            self.visit(f.out_type),
            f.body_string)
        self.funcs[f.name] = f
        return f

    def handleize(self, statevar_type, statevar_name):
        if self.should_handleize and isinstance(statevar_type, syntax.TBag):
            ht = syntax.THandle(statevar_name, statevar_type.t)
            return syntax.TBag(ht)
        return statevar_type

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
        if t.t == "Set":
            return syntax.TSet(self.visit(t.args))
        elif t.t == "Bag":
            return syntax.TBag(self.visit(t.args))
        else:
            self.report_err(t, "unknown type {}".format(t.t))
            return t

    def visit_TRecord(self, t):
        return syntax.TRecord(tuple((f, self.visit(ft)) for f, ft in t.fields))

    def visit_TTuple(self, t):
        return syntax.TTuple(tuple(self.visit(tt) for tt in t.ts))

    def visit_THandle(self, t):
        if t.value_type is None:
            assert self.handleize
            elem = self.env[t.statevar]
            return elem.t
        return syntax.THandle(t.statevar, self.visit(t.value_type))

    def visit_TBool(self, t):
        return t

    def visit_TString(self, t):
        return t

    def visit_TInt(self, t):
        return t

    def visit_TLong(self, t):
        return t

    def visit_TNative(self, t):
        return t

    def visit_TMaybe(self, t):
        return type(t)(self.visit(t.t))

    def visit_TBag(self, t):
        return type(t)(self.visit(t.t))

    def visit_TSet(self, t):
        return type(t)(self.visit(t.t))

    def visit_TMap(self, t):
        return type(t)(self.visit(t.k), self.visit(t.v))

    def ensure_type(self, e, t, msg="expression has type {} instead of {}"):
        if not hasattr(e, "type"):
            self.visit(e)
        if t is not DEFAULT_TYPE and e.type is not DEFAULT_TYPE and e.type != t:
            self.report_err(e, msg.format(pprint(e.type), pprint(t)))

    def is_numeric(self, t):
        return t in [INT, LONG]

    def ensure_numeric(self, e):
        if e.type is DEFAULT_TYPE:
            return
        if not self.is_numeric(e.type):
            self.report_err(e, "expression has non-numeric type {}".format(e.type))

    def numeric_lub(self, t1, t2):
        if t1 == LONG or t2 == LONG:
            return LONG
        return INT

    def get_collection_type(self, e):
        """if e has a collection type, e.g. List<Int>, this returns the inner type, e.g. Int"""
        if e.type is DEFAULT_TYPE:           return DEFAULT_TYPE
        if isinstance(e.type, syntax.TBag):  return e.type.t
        if isinstance(e.type, syntax.TSet):  return e.type.t
        self.report_err(e, "expression has non-collection type {}".format(e.type))
        return DEFAULT_TYPE

    def visit_EUnaryOp(self, e):
        self.visit(e.e)
        if e.op == syntax.UOp.Sum:
            tt = self.get_collection_type(e.e)
            if self.is_numeric(tt) or tt is DEFAULT_TYPE:
                e.type = tt
            else:
                self.report_err(e, "cannot sum {}".format(e.e.type))
                e.type = DEFAULT_TYPE
        elif e.op in [syntax.UOp.AreUnique, syntax.UOp.Empty]:
            self.get_collection_type(e.e)
            e.type = BOOL
        elif e.op == syntax.UOp.Distinct:
            t = self.get_collection_type(e.e)
            e.type = e.e.type
        elif e.op == syntax.UOp.The:
            t = self.get_collection_type(e.e)
            e.type = syntax.TMaybe(t)
        elif e.op in [syntax.UOp.Any, syntax.UOp.All]:
            self.ensure_type(e.e, syntax.TBag(BOOL))
            e.type = BOOL
        elif e.op == syntax.UOp.Length:
            self.get_collection_type(e.e)
            e.type = INT
        elif e.op == syntax.UOp.Not:
            self.ensure_type(e.e, BOOL)
            e.type = BOOL
        elif e.op == "-":
            self.ensure_numeric(e.e)
            e.type = e.e.type
        else:
            raise NotImplementedError(e.op)

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

    def visit_EJust(self, e):
        self.visit(e.e)
        e.type = syntax.TMaybe(e.e.type)

    def visit_EAlterMaybe(self, e):
        self.visit(e.e)
        self.visit(e.f)
        e.type = syntax.TMaybe(e.f.body.type)

    def visit_ECond(self, e):
        self.visit(e.cond)
        self.visit(e.then_branch)
        self.visit(e.else_branch)
        self.ensure_type(e.cond, BOOL)
        self.ensure_type(e.else_branch, e.then_branch.type)
        e.type = e.then_branch.type

    def visit_ELambda(self, e):
        with self.scope():
            self.env[e.arg.id] = e.arg.type
            self.visit(e.body)

    def visit_EBinOp(self, e):
        self.visit(e.e1)
        self.visit(e.e2)
        if e.op in ["==", "!=", "<", "<=", ">", ">="]:
            if not all([t in (INT, LONG) for t in [e.e1.type, e.e2.type]]):
                self.ensure_type(e.e2, e.e1.type)
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
            if e.e1.type in [INT, LONG]:
                self.ensure_numeric(e.e1)
                self.ensure_numeric(e.e2)
                e.type = self.numeric_lub(e.e1.type, e.e2.type)
            else:
                t1 = self.get_collection_type(e.e1)
                t2 = self.get_collection_type(e.e2)
                if t1 != t2:
                    self.report_err(e, "cannot concat {} and {}".format(pprint(e.e1.type), pprint(e.e2.type)))
                e.type = syntax.TBag(t1)
        else:
            raise NotImplementedError(e.op)

    def visit_EFlatten(self, e):
        self.visit(e.e)
        t = self.get_collection_type(e.e)
        if isinstance(t, syntax.TBag):
            e.type = t
        else:
            self.report_err("cannot flatten {}".format(e.e.type))
            e.type = DEFAULT_TYPE

    def visit_EFlatMap(self, e):
        self.visit(e.e)
        t1 = self.get_collection_type(e.e)
        self.visit(e.f)
        self.ensure_type(e.f.arg, t1)
        t2 = self.get_collection_type(e.f.body)
        e.type = e.f.body.type

    def visit_ECall(self, e):
        f = self.funcs.get(e.func) or self.queries.get(e.func)
        if f is None:
            self.report_err(e, "unknown function {}".format(repr(e.func)))

        for a in e.args:
            self.visit(a)

        if f is not None:
            if len(f.args) != len(e.args):
                self.report_err(e, "wrong number of arguments to {}".format(repr(e.func)))
            i = 1
            for arg_decl, arg_val in zip(f.args, e.args):
                arg_name, arg_type = arg_decl
                self.ensure_type(arg_val, arg_type, "argument {} to {} has type {{}} instead of {{}}".format(i, f.name))
                i += 1
            e.type = f.out_type
        else:
            e.type = DEFAULT_TYPE

    def visit_EEmptyList(self, e):
        if not hasattr(e, "type"):
            self.report_err(e, "unable to infer type for empty collection")
        else:
            self.get_collection_type(e)

    def visit_ESingleton(self, e):
        self.visit(e.e)
        e.type = syntax.TBag(e.e.type)

    def visit_EListComprehension(self, e):
        with self.scope():
            for clause in e.clauses:
                self.visit(clause)
            self.visit(e.e)
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
            if e.f in fields:
                e.type = fields[e.f]
            else:
                self.report_err(e, "no field {} on type {}".format(e.f, e.e.type))
                e.type = DEFAULT_TYPE
        elif isinstance(e.e.type, syntax.THandle):
            if e.f == "val":
                e.type = e.e.type.value_type
            else:
                self.report_err(e, "no field {} on type {}".format(e.f, e.e.type))
                e.type = DEFAULT_TYPE
        else:
            self.report_err(e, "cannot get field {} from non-record {}".format(e.f, e.e.type))
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

    def visit_ETuple(self, e):
        for ee in e.es:
            self.visit(ee)
        e.type = syntax.TTuple(tuple(ee.type for ee in e.es))

    def visit_ETupleGet(self, e):
        self.visit(e.e)
        t = e.e.type
        if isinstance(t, syntax.TTuple):
            if e.n >= 0 and e.n < len(t.ts):
                e.type = t.ts[e.n]
            else:
                self.report_err(e, "cannot get element {} from tuple of size {}".format(e.n, len(t.ts)))
                e.type = DEFAULT_TYPE
        else:
            self.report_err(e, "cannot get element from non-tuple")
            e.type = DEFAULT_TYPE

    def visit_EMap(self, e):
        self.visit(e.e)
        elem_type = self.get_collection_type(e.e)
        self.visit(e.f)
        self.ensure_type(e.f.arg, elem_type)
        e.type = syntax.TBag(e.f.body.type)

    def visit_EFilter(self, e):
        self.visit(e.e)
        elem_type = self.get_collection_type(e.e)
        self.visit(e.p)
        self.ensure_type(e.p.arg, elem_type)
        self.ensure_type(e.p.body, BOOL)
        e.type = e.e.type

    def visit_EMakeMap(self, e):
        self.visit(e.e)
        t = self.get_collection_type(e.e)
        self.visit(e.key)
        self.ensure_type(e.key.arg, t)
        self.visit(e.value)
        self.ensure_type(e.value.arg, e.e.type)
        e.type = syntax.TMap(e.key.body.type, e.value.body.type)

    def visit_EMapGet(self, e):
        self.visit(e.map)
        self.visit(e.key)
        if not isinstance(e.map.type, syntax.TMap):
            self.report_err(e, "{} is not a map".format(e.map))
            e.type = DEFAULT_TYPE
        self.ensure_type(e.key, e.map.type.k)
        e.type = e.map.type.v

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
                self.ensure_type(s.args[0], s.target.type)
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
        self.ensure_type(s.rhs, s.lhs.type)

    def visit_SForEach(self, s):
        assert isinstance(s.id, syntax.EVar)
        with self.scope():
            self.visit(s.iter)
            t = self.get_collection_type(s.iter)
            self.env[s.id.id] = t
            self.visit(s.body)

    def visit_SDecl(self, s):
        self.visit(s.val)
        self.env[s.id] = s.val.type

    def visit(self, x):
        res = super().visit(x)
        should_have_type = isinstance(x, syntax.Exp) and not isinstance(x, target_syntax.ELambda)
        if should_have_type and (not hasattr(x, "type") or x.type is None):
            raise Exception(x)
        return res
