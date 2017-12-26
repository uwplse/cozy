from cozy.syntax import Stm, Exp, Type
from cozy.common import declare_case

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
