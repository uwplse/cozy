#!/bin/bash
cd "$(dirname "$0")"

MSG="E"           # enable all error-class messages
MSG="$MSG,W0221"  # differing argument numbers in inherited method
MSG="$MSG,W0222"  # differing signature in inherited method
MSG="$MSG,W0223"  # method is abstract but not overridden
MSG="$MSG,W0231"  # base __init__ not called

exec pylint \
    --reports=n \
    --disable=all \
    --enable="$MSG" \
    $(find src -name '*.py')
