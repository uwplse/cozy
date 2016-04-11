#!/bin/bash

EXIT=0
cd "$(dirname "$0")"

function synth {
    python src/main.py --java 'tests/DataStructure'$2'.java' --java-class 'DataStructure'$2 --java-package tests $1
}

function fail {
    EXIT=1
    echo "*** FAILED ***"
}

function run-test {
    echo "testing $2..."
    JAVA="$1"
    javac "$JAVA" && java -ea "$(sed 's_/_._g' <<<"${JAVA%%.java}")"
}

synth examples/binarysearch BinarySearch
run-test 'tests/BinarySearch.java' 'tests.BinarySearch' || fail
synth examples/hashlookup HashLookup
run-test 'tests/HashLookup.java' 'tests.HashLookup' || fail
synth examples/intervals1 Intervals1
run-test 'tests/Intervals1.java' 'tests.Intervals1' || fail

exit "$EXIT"
