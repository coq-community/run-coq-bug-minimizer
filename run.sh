#!/usr/bin/env bash

set -o pipefail

RC=1

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

function cleanup() {
    cp -f "bug_01.v" "$DIR/bug.v" || RC=$?
    STAMP="$(cat "$DIR/coqbot-request-stamp")"
    if [ -f "$DIR/bug.v" ]; then
        touch "$DIR/build.log" "$DIR/bug.log"
        bash "$DIR/reply-coqbot.sh" "$STAMP" "$FILE" "$DIR/bug.v" "$DIR/build.log" "$DIR/bug.log"
    else
        touch "$DIR/build.log"
        bash "$DIR/reply-coqbot-error.sh" "$STAMP" "$FILE" "$DIR/build.log"
    fi
    exit $RC
}

#trap cleanup SIGINT SIGKILL EXIT

set -x

if [ ! -f "$DIR/build.log.orig" ]; then

#source "$DIR/coqbot.sh" >"$DIR/build.log" 2>&1
source "$DIR/coqbot.sh" 2>&1 | tee "$DIR/build.log"
cp "$DIR/build.log" "$DIR/build.log.orig"

else

    cp "$DIR/build.log.orig" "$DIR/build.log"

fi

set -x

cat "$DIR/build.log"

FILE="$(tac "$DIR/build.log" | grep --max-count=1 -A 1 '^Error' | grep '^File "[^"]*", line [0-9]*, characters [0-9-]*:' | grep -o '^File "[^"]*' | sed 's/^File "//g')"
EXEC_AND_PATH="$(tac "$DIR/build.log" | grep -A 1 -F "$FILE" | grep --max-count=1 -A 1 'MINIMIZER_DEBUG: exec')"
EXEC="$(echo "${EXEC_AND_PATH}" | grep -o 'exec: .*' | sed 's/^exec: //g')"
COQPATH="$(echo "${EXEC_AND_PATH}" | grep -o 'COQPATH=.*' | sed 's/^COQPATH=//g')"

function process_args() {
    passing_prefix="--$1"
    next_is_known=no
    next_next_is_known=no
    while read i; do
        if [ "${next_is_known}" == "yes" ]; then
            echo "$i"
            next_is_known="${next_next_is_known}"
            next_next_is_known=no
        elif [[ "$i" == *".v" ]]; then
            :
        else
            case "$i" in
                -R|-Q)
                    echo "${passing_prefix}${i}"
                    next_is_known=yes
                    next_next_is_known=yes
                    ;;
                -I|-arg)
                    echo "${passing_prefix}${i}"
                    next_is_known=yes
                    ;;
                *)
                    echo "${passing_prefix}-arg=$i"
                    ;;
            esac
        fi
    done
}

function coqpath_to_args() {
    local IFS=:
    for i in $1; do
        echo "-I"
        echo "$i"
        for subdir in $(ls "$i"); do
            if [ -d "$i/$subdir" ]; then
                echo "-Q"
                echo "$i/$subdir"
                echo "$subdir"
            fi
        done
    done
}


FAILING_COQPATH="$COQPATH"
PASSING_COQPATH="$(echo "$COQPATH" | sed 's,/builds/coq/coq-failing/,/builds/coq/coq-passing/,g')"
FAILING_COQC="$(bash -c "echo ${EXEC} | tr ' ' '\n'" | head -1)"
PASSING_COQC="$(bash -c "echo ${EXEC} | tr ' ' '\n'" | head -1 | sed 's,/builds/coq/coq-failing/,/builds/coq/coq-passing/,g')"
FAILING_ARGS="$( (bash -c "echo ${EXEC} | tr ' ' '\n'" | tail -n +2; coqpath_to_args "${FAILING_COQPATH}") | process_args nonpassing)"
PASSING_ARGS="$( (bash -c "echo ${EXEC} | tr ' ' '\n'" | tail -n +2 | sed 's,/builds/coq/coq-failing/,/builds/coq/coq-passing/,g'; coqpath_to_args "${PASSING_COQPATH}") | process_args passing)"
FAILING_COQTOP="$(echo "$FAILING_COQC" | sed 's,bin/coqc,bin/coqtop,g')"
FAILING_COQ_MAKEFILE="$(echo "$FAILING_COQC" | sed 's,bin/coqc,bin/coq_makefile,g')"

(echo "${FAILING_ARGS}"; echo "${PASSING_ARGS}"; echo -l; echo -; echo "$DIR/bug.log") | xargs find-bug.py -y "$FILE" "$DIR/bug_01.v" "$DIR/tmp.v" --no-deps --coqc="${FAILING_COQC}" --coqtop="${FAILING_COQTOP}"  --coq_makefile="${FAILING_COQ_MAKEFILE}" --passing-coqc="${PASSING_COQC}" --passing-base-dir="/builds/coq/coq-passing/_build_ci/" --base-dir="/builds/coq/coq-failing/_build_ci/" && RC=0
