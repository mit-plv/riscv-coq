#!/bin/sh

if [ "$#" -ne 2 ]; then
    echo "Usage: 2 args: directory of dependency to check and expected commit hash"
    exit 1
fi

d=$1

EXPECTED=$2
ACTUAL=`cd $d && git rev-parse HEAD`
if [ "$ACTUAL" != "$EXPECTED" ]; then
    echo "Commit hash of $d does not match: Expected $EXPECTED, but got $ACTUAL"
    exit 1
fi

