#!/bin/sh

#################################################################
#                                                               #
# Copyright (c) 2020 YottaDB LLC and/or its subsidiaries.       #
# All rights reserved.                                          #
#                                                               #
#       This source code contains the intellectual property     #
#       of its copyright holder(s), and is made available       #
#       under a license.  If you do not know the terms of       #
#       the license, please stop and do not read further.       #
#                                                               #
#################################################################

# If this is running in CI, it's in a fresh clone of the repo,
# so `git diff HEAD` will always say there were no changes
if [ -n "$CONTINUOUS_INTEGRATION" ]; then
	COMMIT=HEAD~
else
	COMMIT=HEAD
fi

MISSING_COPYRIGHT="$(git diff --name-only $COMMIT | xargs --no-run-if-empty grep -L "Copyright (c) .*$(date +%Y) YottaDB" -L)"
if [ -n "$MISSING_COPYRIGHT" ]; then
    echo "the following files do not have an up-to-date copyright:"
    for file in $MISSING_COPYRIGHT; do
        echo "- $file"
    done
    exit 1
fi
