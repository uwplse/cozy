"""Tools to define local options.

Many Cozy modules have local options like timeouts and tuning parameters.  It
is convenient for those options to be listed in the module source code, but it
is inconvenient to write code that collects them across the entire codebase.
This module addresses the problem by letting each module declare Option
instances for each of its settings and providing a `setup` to inform a
command-line parser about all Options that have been defined by the program
so far.
"""

# All Option objects that have ever been created.
_OPTS = []

class Option(object):
    def __init__(self, name, type, default, description="", metavar=None):
        assert type in (bool, str, int)
        self.name = name
        self.description = description
        self.type = type
        self.default = default
        self.value = default
        self.metavar = metavar
        _OPTS.append(self)

    def __bool__(self):
        raise Exception(
            "An attempt was made to convert an Option to a boolean. " +
            "If you intended to read the value of this Option, use `_.value`. " +
            "If you intended to check whether this object is None, use `_ is None`.")

def _argname(o):
    if o.type is bool:
        return ("no-" + o.name) if o.default else o.name
    return o.name

def setup(parser):
    for o in _OPTS:
        n = _argname(o)
        if o.type is bool:
            parser.add_argument("--" + n, action="store_true", default=False, help=o.description)
        elif o.type in (str, int):
            parser.add_argument("--" + n, metavar=o.metavar, default=o.default, help=(o.description + " (default={})".format(repr(o.default))) if o.description else "default={}".format(repr(o.default)))

def read(args):
    for o in _OPTS:
        o.value = getattr(args, _argname(o).replace("-", "_"))
        if o.type is bool and o.default:
            o.value = not o.value
        if o.type is int:
            o.value = int(o.value)
