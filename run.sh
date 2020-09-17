#!/usr/bin/env bash

set -o pipefail

RC=1

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
BUG_FILE="$DIR/bug_01.v"

function cleanup() {
    cp -f "${BUG_FILE}" "$DIR/bug.v" || RC=$?
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

trap cleanup SIGINT SIGKILL EXIT

set -x

source "$DIR/coqbot-config.sh"

if [ "${RUN_KIND}" == "coqbot-ci" ]; then
    source "$DIR/coqbot-ci.sh" 2>&1 | tee "$DIR/build.log"
else
    for i in coqc coqtop; do
        pushd "$(dirname "$(which "$i")")"
        wrap_file "$i"
        popd
    done

    source "$DIR/coqbot.sh" 2>&1 | tee "$DIR/build.log"
fi

set -x

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

FILE="$(tac "$DIR/build.log" | grep --max-count=1 -A 1 '^Error' | grep '^File "[^"]*", line [0-9]*, characters [0-9-]*:' | grep -o '^File "[^"]*' | sed 's/^File "//g')"
EXEC_AND_PATH="$(tac "$DIR/build.log" | grep -A 1 -F "$FILE" | grep --max-count=1 -A 1 'MINIMIZER_DEBUG: exec')"
EXEC="$(echo "${EXEC_AND_PATH}" | grep -o 'exec: .*' | sed 's/^exec: //g')"
COQPATH="$(echo "${EXEC_AND_PATH}" | grep -o 'COQPATH=.*' | sed 's/^COQPATH=//g')"

FAILING_COQPATH="$COQPATH"
FAILING_COQC="$(bash -c "echo ${EXEC} | tr ' ' '\n'" | head -1)"
FAILING_ARGS="$( (bash -c "echo ${EXEC} | tr ' ' '\n'" | tail -n +2; coqpath_to_args "${FAILING_COQPATH}") | process_args nonpassing)"

FAILING_COQTOP="$(echo "$FAILING_COQC" | sed 's,bin/coqc,bin/coqtop,g')"
FAILING_COQ_MAKEFILE="$(echo "$FAILING_COQC" | sed 's,bin/coqc,bin/coq_makefile,g')"

PASSING_COQPATH="$(echo "$COQPATH" | sed 's,/builds/coq/coq-failing/,/builds/coq/coq-passing/,g')"
PASSING_COQC="$(bash -c "echo ${EXEC} | tr ' ' '\n'" | head -1 | sed 's,/builds/coq/coq-failing/,/builds/coq/coq-passing/,g')"
PASSING_ARGS="$( (bash -c "echo ${EXEC} | tr ' ' '\n'" | tail -n +2 | sed 's,/builds/coq/coq-failing/,/builds/coq/coq-passing/,g'; coqpath_to_args "${PASSING_COQPATH}") | process_args passing)"

{
    echo "${FAILING_ARGS}"
    echo --coqc="${FAILING_COQC}"
    echo --coqtop="${FAILING_COQTOP}"
    echo --coq_makefile="${FAILING_COQ_MAKEFILE}"
    echo --base-dir="/builds/coq/coq-failing/_build_ci/"
    if [ "${PASSING_COQC}" != "${FAILING_COQC}" ]; then
        # are running with two versions
        echo "${PASSING_ARGS}"
        echo --passing-coqc="${PASSING_COQC}"
        echo --passing-base-dir="/builds/coq/coq-passing/_build_ci/"
    fi
    echo -l
    echo -
    echo "$DIR/bug.log"
} | xargs find-bug.py -y "$FILE" "${BUG_FILE}" "$DIR/tmp.v" --no-deps && RC=0
