#!/bin/bash

function err {
    echo -e "\033[1;31m$1\033[0;0m"
}

function require-program {
    echo -n "checking for $1... "
    if ! which $1; then
        err "missing!"
        return 1
    fi
}

function check-python-version {
    echo -n "checking for python version >= 3.4... "
    VERSION="$(python3 -c 'import sys; print(sys.version); sys.exit(sys.version_info < (3,4) or sys.version_info >= (4,))' | head -n1)"
    if [[ $? != 0 ]]; then
        err "found $VERSION"
        return 1
    else
        echo "$VERSION"
    fi
}

function check-z3 {
    echo -n "checking for z3 python module... "
    if ! python3 -c "import z3" >/dev/null 2>&1; then
        err "not found"
        return 1
    else
        echo "found"
    fi
}

function check-z3-version {
    echo -n "checking for z3 version >= 4.4... "
    VERSION="$(python3 -c 'import z3,sys; print(z3.get_version_string()); sys.exit(z3.get_version() < (4,4))')"
    if [[ $? != 0 ]]; then
        err "found $VERSION"
        return 1
    else
        echo "$VERSION"
    fi
}

require-program python3 && (check-python-version; (check-z3 && check-z3-version))

if [[ $? == 0 ]]; then
    echo "SUCCESS!"
else
    exit 1
fi
