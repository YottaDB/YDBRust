#!/bin/sh

MISSING_COPYRIGHT="$(git diff --name-only HEAD | xargs grep -L "Copyright (c) .*$(date +%Y) YottaDB" -L)"
if [ -n "$MISSING_COPYRIGHT" ]; then
    echo "the following files do not have an up-to-date copyright:"
    for file in $MISSING_COPYRIGHT; do
        echo "- $file"
    done
fi
