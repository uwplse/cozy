"""Definitions for expression pools.

During synthesis, expressions belong to one of two pools: the runtime pool for
expressions executed when the method is called, and the state pool for
expressions that are part of the abstraction relation.

This module declares constants for the two pools and a `pool_name` function to
print them.
"""

from enum import Enum

class Pool(Enum):
    STATE_POOL   = 0
    RUNTIME_POOL = 1

STATE_POOL   = Pool.STATE_POOL
RUNTIME_POOL = Pool.RUNTIME_POOL
ALL_POOLS = tuple(Pool)

_POOL_NAMES = {
    STATE_POOL: "state",
    RUNTIME_POOL: "runtime",
}
def pool_name(pool):
    return _POOL_NAMES[pool]
