#!/usr/bin/env bash

RC=1

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

function cleanup() {
    cp -f "bug_01.v" "$DIR/bug.v"
    exit $RC
}

trap cleanup SIGINT SIGKILL EXIT

set -x

source "$DIR/coqbot.sh" 2>"$DIR/log"

set -e

FILE="$(grep '^File "[^"]*", line [0-9]*, characters [0-9-]*:' log | grep -o '^File "[^"]*' | sed 's/^File "//g')"

(yes "y" || true) | find-bug.py "${FILE}" bug_01.v tmp.v --inline-user-contrib -l - "$DIR/bug.log" && RC=0
cleanup
