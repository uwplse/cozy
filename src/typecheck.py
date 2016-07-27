from common import Visitor
import syntax
from syntax_tools import pprint

def typecheck(ast, env=None):
    """
    Typecheck the syntax tree.
    This procedure attaches a .type attribute to every expression, and returns
    a list of type errors (or an empty list if everything typechecks properly).
    """
    typechecker = Typechecker(env or ())
    typechecker.visit(ast)
    return typechecker.errors

INT = syntax.TInt()
LONG = syntax.TLong()
DEFAULT_TYPE = None
BOOL = syntax.TBool()
STRING = syntax.TString()

class Typechecker(Visitor):

    def __init__(self, env):
        self.tenv = {
            "Int": INT,
            "Bound": INT, # TODO?
            "Long": LONG,
            "Bool": BOOL,
            "String": STRING }

        self.env = dict(env)
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
        for name, t in spec.statevars:
            self.env[name] = self.handleize(self.visit(t), name)
        spec.statevars = [(name, self.env[name]) for (name, t) in spec.statevars]
        for e in spec.assumptions:
            self.ensure_type(e, BOOL)
        for op in spec.methods:
            self.visit(op)

    def handleize(self, collection_type, statevar_name):
        if isinstance(collection_type, syntax.TBag):
            ht = syntax.THandle(statevar_name)
            ht.value_type = collection_type.t
            return syntax.TBag(ht)
        else:
            self.report_err(statevar_name, "only bag types are supported")

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
        if t.t == "List":
            return syntax.TList(self.visit(t.args))
        elif t.t == "Set":
            return syntax.TSet(self.visit(t.args))
        elif t.t == "Bag":
            return syntax.TBag(self.visit(t.args))
        else:
            self.report_err(t, "unknown type {}".format(t.t))
            return t

    def visit_TRecord(self, t):
        return syntax.TRecord(tuple((f, self.visit(ft)) for f, ft in t.fields))

    def visit_THandle(self, t):
        return t

    def visit_TBool(self, t):
        return t

    def ensure_type(self, e, t):
        if not hasattr(e, "type"):
            self.visit(e)
        if e.type != t:
            self.report_err(e, "expression has type {} instead of {}".format(e.type, t))

    def get_collection_type(self, e):
        """if e has a collection type, e.g. List<Int>, this returns the inner type, e.g. Int"""
        if isinstance(e.type, syntax.TList): return e.type.t
        if isinstance(e.type, syntax.TBag):  return e.type.t
        if isinstance(e.type, syntax.TSet):  return e.type.t
        self.report_err(e, "expression has non-collection type {}".format(e.type))
        return DEFAULT_TYPE

    def visit_EUnaryOp(self, e):
        self.visit(e.e)
        if e.op == "sum":
            e.type = INT
        elif e.op in ["unique", "empty"]:
            self.get_collection_type(e.e)
            e.type = BOOL
        elif e.op == "distinct":
            t = self.get_collection_type(e.e)
            e.type = syntax.TSet(t)
        elif e.op in ["some", "min", "max"]:
            t = self.get_collection_type(e.e)
            e.type = t
        elif e.op == "len":
            self.get_collection_type(e.e)
            e.type = INT
        elif e.op == "not":
            self.ensure_type(e.e, BOOL)
            e.type = BOOL
        elif e.op == "singleton":
            e.type = syntax.TSet(e.e.type)
        elif e.op == "iterator":
            self.get_collection_type(e.e)
            e.type = e.e.type
        else:
            raise NotImplementedError(e.op)

    def visit_EBool(self, e):
        e.type = BOOL

    def visit_ENum(self, e):
        e.type = INT

    def ensure_numeric(self, e):
        if e.type not in [INT, LONG]:
            self.report_err(e, "expression has non-numeric type {}".format(e.type))

    def numeric_lub(self, t1, t2):
        if t1 == LONG or t2 == LONG:
            return LONG
        return INT

    def visit_EBinOp(self, e):
        self.visit(e.e1)
        self.visit(e.e2)
        if e.op in ["==", "!=", "<", "<=", ">", ">="]:
            if not all([t in (INT, LONG) for t in [e.e1.type, e.e2.type]]):
                self.ensure_type(e.e2, e.e1.type)
            e.type = BOOL
        elif e.op in ["and", "or", "=>"]:
            self.ensure_type(e.e1, BOOL)
            self.ensure_type(e.e2, BOOL)
            e.type = BOOL
        elif e.op == "in":
            t = self.get_collection_type(e.e2)
            self.ensure_type(e.e1, t)
            e.type = BOOL
        elif e.op in ["+", "-"]:
            self.ensure_numeric(e.e1)
            self.ensure_numeric(e.e2)
            e.type = self.numeric_lub(e.e1.type, e.e2.type)
        elif e.op in ["union", "intersection"]:
            e1set = isinstance(e.e1.type, syntax.TSet)
            e2set = isinstance(e.e1.type, syntax.TSet)
            e1set or self.report_err(e.e1, "not a set")
            e2set or self.report_err(e.e2, "not a set")
            if e1set and e2set:
                self.ensure_type(e.e2, e.e1.type)
                e.type = e.e1.type
            else:
                e.type = DEFAULT_TYPE
        else:
            raise NotImplementedError(e.op)

    def visit_ECall(self, e):
        for a in e.args:
            self.visit(a)
        if e.func == "bag":
            if len(e.args) == 1:
                t = self.get_collection_type(e.args[0])
                e.type = syntax.TBag(t)
            else:
                self.report_err(e, "function called with {} args instead of 1".format(len(e.args)))
                e.type = syntax.TBag(DEFAULT_TYPE)
        else:
            raise NotImplementedError(e.func)

    def visit_EEmptyList(self, e):
        e.type = syntax.TList(None)

    def visit_EListComprehension(self, e):
        with self.scope():
            for clause in e.clauses:
                self.visit(clause)
            self.visit(e.e)
        e.type = syntax.TList(e.e.type)

    def visit_EMakeRecord(self, e):
        fields = []
        for f, val in e.fields:
            self.visit(val)
            fields.append((f, val.type))
        e.type = syntax.TRecord(fields)

    def visit_CPull(self, c):
        self.visit(c.e)
        t = self.get_collection_type(c.e)
        self.env[c.id] = t

    def visit_CCond(self, c):
        self.ensure_type(c.e, BOOL)

    def visit_EGetField(self, e):
        self.visit(e.e)
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
        if hasattr(e, "type"):
            pass
        elif e.id in self.env:
            e.type = self.env[e.id]
        else:
            self.report_err(e, "no var {} in scope".format(e.id))
            e.type = DEFAULT_TYPE

    def visit_ETuple(self, e):
        ts = [self.visit(ee) for ee in e.es]
        e.type = syntax.TTuple(ts)

    def visit_Op(self, op):
        op.args = [(name, self.visit(t)) for (name, t) in op.args]
        with self.scope():
            for name, t in op.args:
                self.env[name] = self.visit(t)
            self.visit(op.body)

    def visit_Query(self, q):
        q.args = [(name, self.visit(t)) for (name, t) in q.args]
        with self.scope():
            for name, t in q.args:
                self.env[name] = self.visit(t)
            self.visit(q.ret)

    def visit_SCall(self, s):
        self.visit(s.target)
        if s.func == "add":
            elem_type = self.get_collection_type(s.target)
            var = s.target.id
            if len(s.args) != 1:
                self.report_err(s, "add takes exactly 1 argument")
            if len(s.args) > 0:
                self.ensure_type(s.args[0], elem_type)
        elif s.func == "remove":
            elem_type = self.get_collection_type(s.target)
            var = s.target.id
            if len(s.args) != 1:
                self.report_err(s, "remove takes exactly 1 argument")
            if len(s.args) > 0:
                self.ensure_type(s.args[0], elem_type)
        else:
            self.report_err(s, "unknown function {}".format(s.func))
