from . import heaps

_lookup = { }
def _register(o):
    for t in o.owned_types():
        _lookup[t] = o

_register(heaps.Heaps())

def extension_handler(t):
    return _lookup.get(t)
