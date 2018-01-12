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
