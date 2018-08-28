from . import heaps

_handlers = []
_lookup = { }
def _register(o):
    _handlers.append(o)
    for t in o.owned_types():
        _lookup[t] = o

_register(heaps.Heaps())

def extension_handler(t):
    return _lookup.get(t)

def all_extension_handlers():
    return _handlers
