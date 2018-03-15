from contextlib import contextmanager

from cozy.syntax import Stm, Exp, Type
from cozy.common import declare_case, Visitor

INDENT = "  "

SEscape = declare_case(Stm, "SEscape", ["body_string", "arg_names", "args"])
EEscape = declare_case(Exp, "EEscape", ["body_string", "arg_names", "args"])
TArray  = declare_case(Type, "TArray", ["t"])

def indent_lines(s, indent):
    """
    Prepends the given indentation string to the beginning of each line of the
    given string.
    """
    return '\n'.join(indent + line for line in s.splitlines())

class CodeGenerator(Visitor):

    def __init__(self, out):
        self.out = out
        self.indent = 0

    def get_indent(self):
        return INDENT * self.indent

    def write(self, *parts):
        for p in parts:
            self.out.write(p)

    def write_stmt(self, *parts):
        self.begin_statement()
        self.write(*parts)
        self.end_statement()

    def begin_statement(self):
        for i in range(self.indent):
            self.write(INDENT)

    def end_statement(self):
        self.write("\n")

    @contextmanager
    def indented(self):
        self.indent += 1
        yield
        self.indent -= 1

    @contextmanager
    def deindented(self):
        self.indent -= 1
        yield
        self.indent += 1

    @contextmanager
    def block(self):
        self.write("{")
        self.end_statement()
        with self.indented():
            yield
        self.begin_statement()
        self.write("}")
