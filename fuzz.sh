#!/bin/bash
cd "$(dirname "$0")"
export PYTHONPATH="src:$PYTHONPATH"
exec python tests/fuzz.py "$@"
