Pool = int
STATE_POOL   = 0
RUNTIME_POOL = 1
ALL_POOLS = (STATE_POOL, RUNTIME_POOL)

_POOL_NAMES = ("state", "runtime")
def pool_name(pool):
    return _POOL_NAMES[pool]
