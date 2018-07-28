"""
Basic generation of RPython.

The generated code will depend on rlib.
"""

from contextlib import contextmanager

from cozy.codegen.misc import CodeGenerator
from cozy.syntax import UOp

class RPythonPrinter(CodeGenerator):

    needsSum = False

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
        """
        Parenthesize something.
        """

        self.write("(")
        yield
        self.write(")")

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

    def visit_EUnaryOp(self, node):
        op = node.op
        if op == UOp.Sum:
            self.needsSum = True
            self.write("_sum(")
            self.visit(node.e)
            self.write(")")
        else:
            import pdb; pdb.set_trace()
            assert False, "Unhandled unary operation while writing RPython"

    def visit_EBinOp(self, node):
        op = node.op
        if op in (">", "+"):
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

    def visit_SNoOp(self, _):
        self.write_stmt("pass")

    def visit_SSeq(self, node):
        self.visit(node.s1)
        self.visit(node.s2)

    def visit_SDecl(self, node):
        self.begin_statement()
        self.write(node.id, " = ")
        self.visit(node.val)
        self.end_statement()

    def visit_SForEach(self, node):
        self.begin_statement()
        self.write("for ")
        self.visit(node.id)
        self.write(" in ")
        self.visit(node.iter)
        self.write(":")
        self.end_statement()
        with self.indented():
            self.visit(node.body)

    def visit_SAssign(self, node):
        self.begin_statement()
        self.visit(node.lhs)
        self.write(" = ")
        self.visit(node.rhs)
        self.end_statement()

    def visit_SCall(self, node):
        self.begin_statement()
        self.visit(node.target)
        self.write(".", node.func)
        with self.parens():
            for arg in node.args:
                self.visit(arg)
                self.write(", ")
        self.end_statement()

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
            self.begin_statement()
            self.write("return ")
            self.visit(node.ret)
            self.end_statement()

    def visit_Spec(self, spec, state_exps, sharing, abstract_state=()):
        self.write_stmt("from rpython.rlib.rbigint import BigInt")

        with self.python_block("class ", spec.name, "(object)"):
            init_args = ", ".join([name for name, _ in abstract_state])
            with self.python_block("def __init__(self, ", init_args, ")"):
                for name, exp in state_exps.items():
                    self.begin_statement()
                    self.write("self.", name, " = ")
                    self.visit(exp)
                    self.end_statement()

            for meth in spec.methods:
                self.visit(meth)

        if self.needsSum:
            with self.python_block("def _sum(it)"):
                self.write_stmt("def rv = 0")
                with self.python_block("for x in it"):
                    self.write_stmt("rv += x")
                self.write_stmt("return rv")
