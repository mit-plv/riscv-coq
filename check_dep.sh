#!/bin/sh

if [ "$#" -ne 1 ]; then
    echo "Usage: 1 arg which is the name of the dependency to check"
    exit 1
fi

d=$1

echo "riscv-coq: Skipping dependency check for $d"
exit 0

EXPECTED=`cat deps/$d`
ACTUAL=`cd ../$d && git rev-parse HEAD`
if [ "$ACTUAL" != "$EXPECTED" ]; then
    echo "Commit hash of $d does not match: Expected $EXPECTED, but got $ACTUAL"
    exit 1
fi

