from collections import OrderedDict

from cozy.common import nested_dict, find_one, typechecked
from cozy.target_syntax import Exp, EVar, EStateVar
from cozy.syntax_tools import free_vars, pprint, alpha_equivalent
from cozy.pools import RUNTIME_POOL, STATE_POOL, ALL_POOLS
from cozy.cost_model import Cost
from cozy.opts import Option

enforce_wf = Option("enforce-cache-wf", bool, False)

class NatDict(object):
    def __init__(self, factory):
        self.factory = factory
        self.data = []
    def get(self, i, default=None):
        data = self.data
        if i < 0 or i >= len(data):
            return default
        return data[i]
    def __getitem__(self, i):
        self._extend(i)
        return self.data[i]
    def __setitem__(self, i, val):
        self._extend(i)
        self.data[i] = val
    def values(self):
        return iter(self.data)
    def keys(self):
        return range(len(self.data))
    def items(self):
        data = self.data
        for i in range(len(data)):
            yield (i, data[i])
    def _extend(self, n):
        data = self.data
        if n < len(data):
            return
        factory = self.factory
        data.extend(factory() for i in range(len(data), n + 1))

class Cache(object):
    def __init__(self, binders : [EVar], args : [EVar], items : [(Exp, int)]=None):
        # self.data[pool][type_tag][type][size] is list of exprs
        self.data = [nested_dict(2, lambda: NatDict(list)) for i in range(len(ALL_POOLS))]
        self.size = 0
        self.binders = set(binders)
        self.args = set(args)
        if items:
            for (e, size) in items:
                self.add(e, size)
    def tag(self, t):
        return type(t)
    def is_tag(self, t):
        return isinstance(t, type)
    def contains(self, e, pool):
        return find_one(self.find(pool=pool, type=e.type), lambda x: alpha_equivalent(x, e)) is not None
    def add(self, e, size, pool):
        if isinstance(e, EStateVar) and self.contains(e.e, STATE_POOL):
            return # already implicitly exists
        if enforce_wf.value:
            assert not self.contains(e, pool)
            if pool == STATE_POOL:
                assert not isinstance(e, EStateVar), "adding {} to state pool".format(pprint(e))
                assert not any(v in self.args for v in free_vars(e)), "bad vars: {}".format(pprint(e))
            else:
                # state vars must be wrapped
                from cozy.syntax_tools import enumerate_fragments
                z = e
                dirty = True
                while dirty:
                    dirty = False
                    for (_, x, r, _) in enumerate_fragments(z):
                        if isinstance(x, EStateVar):
                            from cozy.target_syntax import ZERO
                            z = r(ZERO)
                            dirty = True
                            break
                bad = find_one(free_vars(z), lambda v: not (v in self.binders or v in self.args))
                assert not bad, "state var `{}` not wrapped in: {!r}".format(bad.id, e)
        self.data[pool][self.tag(e.type)][e.type][size].append(e)
        self.size += 1
    def evict(self, e, size, pool):
        try:
            self.data[pool][self.tag(e.type)][e.type][size].remove(e)
            self.size -= 1
        except ValueError:
            # this happens if e is not in the list, which is fine
            pass
    def _raw_find(self, pool, type=None, size=None):
        type_tag = None
        if type is not None:
            if self.is_tag(type):
                type_tag = type
                type = None
            else:
                type_tag = self.tag(type)
        for x in (self.data[pool].values() if type_tag is None else [self.data[pool].get(type_tag, {})]):
            for y in (x.values() if type is None else [x.get(type, {})]):
                for z in (y.values() if size is None else [y.get(size, [])]):
                    yield from z
    def find(self, pool, type=None, size=None):
        res = []
        res.extend(self._raw_find(pool, type, size))
        if pool == RUNTIME_POOL:
            for e in self._raw_find(STATE_POOL, type, size):
                if all(v not in self.binders for v in free_vars(e)):
                    res.append(EStateVar(e).with_type(e.type))
        return res
    def types(self):
        for p in ALL_POOLS:
            for y in self.data[p].values():
                yield from y.keys()
    def __iter__(self):
        for p in ALL_POOLS:
            for x in self.data[p].values():
                for y in x.values():
                    for (size, es) in y.items():
                        for e in es:
                            yield (e, size, p)
    def __len__(self):
        return self.size
    def random_sample(self, n):
        import random
        es = [ e for (e, size, pool) in self ]
        return random.sample(es, min(n, len(es)))

class SeenSet(object):
    def __init__(self):
        self.data = OrderedDict() # maps (pool, fingerprint) to list of (e, size, cost)
    def _find(self, pool, fingerprint, create=False):
        key = (pool, fingerprint)
        l = self.data.get(key)
        if l is None:
            if create:
                l = []
                self.data[key] = l
            else:
                return ()
        return l
    @typechecked
    def add(self, e : Exp, pool : int, fingerprint : tuple, size : int, cost : Cost):
        l = self._find(pool, fingerprint, create=True)
        assert all(v[0] != e for v in l)
        l.append((e, size, cost))
    def find_all(self, pool, fingerprint):
        """yields (e, size, cost) tuples"""
        yield from self._find(pool, fingerprint)
    def find_one(self, pool, fingerprint):
        """returns first-seen (e, size, cost) with given pool and fingerprint, or None"""
        for x in self.find_all(pool, fingerprint):
            return x
        return None
    def items(self):
        """yields (e, pool, fingerprint, size, cost) tuples"""
        for (pool, fp), l in self.data.items():
            for (e, size, cost) in l:
                yield (e, pool, fp, size, cost)
    def remove(self, e, pool, fingerprint):
        l = self._find(pool, fingerprint)
        for i in range(len(l)):
            if l[i][0] is e:
                del l[i]
                return
    def clear(self):
        self.data.clear()
