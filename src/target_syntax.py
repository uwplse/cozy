"""
While the syntax module declares the core _input_ language, this module declares
additional syntax extensions that can appear in the _target_ language: the
primitives the tool can output and use during synthesis.
"""

from syntax import *
from common import declare_case, typechecked

# Holes for synthesized expressions
EHole = declare_case(Exp, "EHole", ["name", "type", "builder"])

# Lambdas
EApp = declare_case(Exp, "EApp", ["f", "arg"])
class ELambda(Exp):
    @typechecked
    def __init__(self, arg : EVar, body : Exp):
        self.arg = arg
        self.body = body
    def apply_to(self, arg):
        from syntax_tools import subst
        return subst(self.body, { self.arg.id : arg })
    def children(self):
        return (self.arg, self.body)
    def __repr__(self):
        return "ELambda{}".format(repr(self.children()))

# Bag transformations
EMap     = declare_case(Exp, "EMap", ["e", "f"])
EFilter  = declare_case(Exp, "EFilter", ["e", "p"])
EFlatten = declare_case(Exp, "EFlatten", ["e"]) # aka concat: Bag<Bag<T>> -> Bag<T>

# Maps
EMakeMap   = declare_case(Exp, "EMakeMap", ["e", "key", "value"])
EMapGet    = declare_case(Exp, "EMapGet", ["map", "key"])
SMapUpdate = declare_case(Stm, "SMapUpdate", ["map", "key", "val_var", "change"])
