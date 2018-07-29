"""
Basic generation of RPython.

The generated code will depend on rlib.
"""

from contextlib import contextmanager
from collections import defaultdict

from cozy.codegen.misc import CodeGenerator

class RPythonPrinter(CodeGenerator):

    def __init__(self, *args, **kwargs):
        super(RPythonPrinter, self).__init__(*args, **kwargs)

        self.needs = defaultdict(bool)

    @contextmanager
    def python_block(self, *args):
        """
        Write a block delimited in the Python style by a trailing colon.
        """

        self.begin_statement()
        self.write(*args, ":")
        self.end_statement()
        with self.indented():
            yield

    @contextmanager
    def parens(self):
        self.write("(")
        yield
        self.write(")")

    @contextmanager
    def stmt(self):
        self.begin_statement()
        yield
        self.end_statement()

    def visit_ENum(self, node):
        self.write(str(node.val))

    def visit_EBool(self, node):
        self.write("True" if node.val else "False")

    def visit_EEmptyList(self, _):
        self.write("[]")

    def visit_ESingleton(self, node):
        self.write("[")
        self.visit(node.e)
        self.write("]")

    def visit_EVar(self, node):
        self.write(node.id)

    def emit_unary(self, op, e):
        self.needs[op] = True
        self.write("_", op, "(")
        self.visit(e)
        self.write(")")

    def visit_EUnaryOp(self, node):
        op = node.op
        if op in ("distinct", "sum"):
            self.emit_unary(op, node.e)
        elif op == "not":
            self.write("not ")
            self.visit(node.e)
        elif op == "empty":
            self.write("not bool(")
            self.visit(node.e)
            self.write(")")
        else:
            import pdb; pdb.set_trace()
            assert False, "Unhandled unary operation while writing RPython"

    def visit_EBinOp(self, node):
        op = node.op
        if op in (">", "<", "+", "-", "==", "in", "and", "or"):
            with self.parens():
                self.visit(node.e1)
                self.write(" ", op, " ")
                self.visit(node.e2)
        else:
            import pdb; pdb.set_trace()
            assert False, "Unhandled binary operation while writing RPython"

    def visit_ECond(self, node):
        self.visit(node.then_branch)
        self.write(" if ")
        self.visit(node.cond)
        self.write(" else ")
        self.visit(node.else_branch)

    def visit_EMap(self, node):
        f = node.f
        self.write("[")
        self.visit(f.body)
        self.write(" for ")
        # Hack: Write the lambda's arg as if it were an expr. This is close
        # enough for now but definitely wrong. ~ C.
        self.visit(f.arg)
        self.write(" in ")
        self.visit(node.e)
        self.write("]")

    def visit_EFilter(self, node):
        p = node.p
        self.write("[")
        # Double hack! Abuse the arg again.
        self.visit(p.arg)
        self.write(" for ")
        self.visit(p.arg)
        self.write(" in ")
        self.visit(node.e)
        self.write(" if ")
        self.visit(p.body)
        self.write("]")

    def visit_EMakeMap2(self, node):
        f = node.value
        self.write("[(")
        self.visit(f.arg)
        self.write(", ")
        self.visit(f.body)
        self.write(") for ")
        self.visit(f.arg)
        self.write(" in ")
        self.visit(node.e)
        self.write("]")

    def visit_EMapGet(self, node):
        self.visit(node.map)
        self.write("[")
        self.visit(node.key)
        self.write("]")

    def visit_SNoOp(self, _):
        self.write_stmt("pass")

    def visit_SSeq(self, node):
        self.visit(node.s1)
        self.visit(node.s2)

    def visit_SDecl(self, node):
        with self.stmt():
            self.write(node.id, " = ")
            self.visit(node.val)

    def visit_SForEach(self, node):
        with self.stmt():
            self.write("for ")
            self.visit(node.id)
            self.write(" in ")
            self.visit(node.iter)
            self.write(":")
        with self.indented():
            self.visit(node.body)

    def visit_SAssign(self, node):
        with self.stmt():
            self.visit(node.lhs)
            self.write(" = ")
            self.visit(node.rhs)

    def visit_SCall(self, node):
        with self.stmt():
            self.visit(node.target)
            self.write(".", node.func)
            with self.parens():
                for arg in node.args:
                    self.visit(arg)
                    self.write(", ")

    def visit_SMapDel(self, node):
        with self.stmt():
            self.write("del ")
            self.visit(node.map)
            self.write("[")
            self.visit(node.key)
            self.write("]")

    def visit_SMapUpdate(self, node):
        with self.stmt():
            self.visit(node.val_var)
            self.write(" = ")
            self.visit(node.map)
            self.write("[")
            self.visit(node.key)
            self.write("]")
        self.visit(node.change)
        # Writeback.
        with self.stmt():
            self.visit(node.map)
            self.write("[")
            self.visit(node.key)
            self.write("] = ")
            self.visit(node.val_var)

    def visit_Op(self, node):
        if node.assumptions:
            import pdb; pdb.set_trace()
        args = ", ".join([name for name, _ in node.args])
        with self.python_block("def ", node.name, "(self, ", args, ")"):
            # Since the body is a statement, we don't need to start the
            # statement right here. Just go straight to the visitor. ~ C.
            self.visit(node.body)

    def visit_Query(self, node):
        if node.assumptions:
            import pdb; pdb.set_trace()
        args = ", ".join([name for name, _ in node.args])
        with self.python_block("def ", node.name, "(self, ", args, ")"):
            with self.stmt():
                self.write("return ")
                self.visit(node.ret)

    def visit_Spec(self, spec, state_exps, sharing, abstract_state=()):
        self.write_stmt("from rpython.rlib.objectmodel import specialize")

        with self.python_block("class ", spec.name, "(object)"):
            init_args = ", ".join([name for name, _ in abstract_state])
            with self.python_block("def __init__(self, ", init_args, ")"):
                for name, exp in state_exps.items():
                    with self.stmt():
                        self.write("self.", name, " = ")
                        self.visit(exp)

            for meth in spec.methods:
                self.visit(meth)

        for op, b in self.needs.items():
            if not b:
                continue
            # Suddenly, globals()! These helpers are textually defined at the
            # end of the module. ~ C.
            self.write(globals()[op.upper()])

DISTINCT = """
@specialize.call_location()
def _distinct(it):
    # Use a dict to simulate a set in RPython. ~ C.
    s = {}
    rv = []
    for x in it:
        if x not in s:
            rv.append(x)
            s[x] = None
    return rv
"""

SUM = """
@specialize.call_location()
def _sum(it):
    rv = 0
    for x in it:
        rv += x
    return rv
"""
