#!/usr/bin/env bash
# Should be invoked from run.sh

set -e -o pipefail

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

source "$DIR/coqbot-config.sh"

set -x

su -c 'apt-get update -y'
su -c 'apt-get install -y sudo'

sudo chmod a+rw .

git clone https://github.com/JasonGross/coq-tools.git

if [ -z "${PYTHON}" ]; then
    PYTHON="$(which python3 || which python)"
fi

# Kludge for quicker running locally
if [ ! -f "$DIR/build.log.orig" ]; then
    if [ "${RUN_KIND}" == "coqbot-ci" ]; then
        source "$DIR/coqbot-ci.sh" 2>&1 | tee "$DIR/build.log"
    else
        for i in coqc coqtop; do
            pushd "$(dirname "$(which "$i")")"
            wrap_file "$i"
            popd
        done

        source "$DIR/coqbot.sh" 2>&1 | tee "$DIR/build.log" || true
    fi
else
    cp -f "$DIR/build.log.orig" "$DIR/build.log"
fi

set -x

function process_args() {
    passing_prefix=""
    prefixed_arg="--arg"
    if [ ! -z "$1" ]; then
        passing_prefix="--$1"
        prefixed_arg="--$1-arg"
    fi
    known_v_file="$2"
    next_is_known=no
    next_next_is_known=no
    prev_load=""
    found_known_v_file=no
    while read i; do
        if [[ "$i" == *".v" ]] && [ "$(readlink -f "${known_v_file}")" == "$(readlink -f "$i")" ]; then
            found_known_v_file=yes
        fi
        if [ ! -z "${prev_load}" ]; then
            if [ "${found_known_v_file}" == "yes" ]; then
                : # we want to skip over loading the file which is buggy, and any loads which come after it, but we want to load files that come before it
            else
                echo "${prev_load}"
                echo "${prefixed_arg}=$i"
            fi
            prev_load=""
            next_is_known="${next_next_is_known}"
            next_next_is_known=no
        elif [ "${next_is_known}" == "yes" ]; then
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
                -I)
                    echo "${passing_prefix}${i}"
                    next_is_known=yes
                    ;;
                -arg)
                    echo "${prefixed_arg}"
                    next_is_known=yes
                    ;;
                -l|-lv|-load-vernac-source|-load-vernac-source-verbose)
                    prev_load="${prefixed_arg}=$i"
                    next_is_known=yes
                    ;;
                -batch)
                    # we already transform coqtop to coqc as necessary, so we can safely ignore -batch
                    ;;
                *)
                    echo "${prefixed_arg}=$i"
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
EXEC="$(echo "${EXEC_AND_PATH}" | grep 'MINIMIZER_DEBUG: exec' | grep -o 'exec:\? .*' | sed 's/^exec:\? //g')"
COQPATH="$(echo "${EXEC_AND_PATH}" | grep -v 'MINIMIZER_DEBUG: exec' | grep -o 'COQPATH=.*' | sed 's/^COQPATH=//g')"

FAILING_COQPATH="$COQPATH"
# some people (like Iris) like to use `coqtop -batch -lv` or similar to process a .v file, so we replace coqtop with coqc
FAILING_COQC="$(bash -c "echo ${EXEC} | tr ' ' '\n'" | head -1 | sed 's,bin/coqtop,bin/coqc,g')"

FAILING_COQTOP="$(echo "$FAILING_COQC" | sed 's,bin/coqc,bin/coqtop,g')"
FAILING_COQ_MAKEFILE="$(cd "$(dirname "${FAILING_COQC}")" && readlink -f coq_makefile)"

PASSING_COQPATH="$(echo "$COQPATH" | sed "s,\(${CI_BASE_BUILD_DIR}\)/coq-failing/,\\1/coq-passing/,g")"
PASSING_COQC="$(bash -c "echo ${EXEC} | tr ' ' '\n'" | head -1 | sed "s,\(${CI_BASE_BUILD_DIR}\)/coq-failing/,\\1/coq-passing/,g" | sed 's,bin/coqtop,bin/coqc,g')"

if [ "${PASSING_COQC}" != "${FAILING_COQC}" ]; then
    # we are running with two versions
    NONPASSING_PREFIX="nonpassing"
else
    # we are running only with one version of coqc, so the minimizer doesn't support --nonpassing prefixes
    NONPASSING_PREFIX=""
fi

FAILING_ARGS="$( (bash -c "echo ${EXEC} | tr ' ' '\n'" | tail -n +2; coqpath_to_args "${FAILING_COQPATH}") | process_args "${NONPASSING_PREFIX}" "${FILE}")"
PASSING_ARGS="$( (bash -c "echo ${EXEC} | tr ' ' '\n'" | tail -n +2 | sed "s,\(${CI_BASE_BUILD_DIR}\)/coq-failing/,\\1/coq-passing/,g"; coqpath_to_args "${PASSING_COQPATH}") | process_args passing "${FILE}")"

mkdir -p "$(dirname "${BUG_FILE}")"
mkdir -p "$(dirname "${TMP_FILE}")"

cd "$(dirname "${BUG_FILE}")"

for VAR in FAILING_COQC FAILING_COQTOP FAILING_COQ_MAKEFILE PASSING_COQC; do
    if [ ! -x "${!VAR}" ]; then
        echo "Error: Could not find ${VAR} ('${!VAR}')" | tee -a "$DIR/bug.log" >&2
        echo "Files in '$(dirname ${!VAR})':" | tee -a "$DIR/bug.log" >&2
        find "$(dirname ${!VAR})" | tee -a "$DIR/bug.log" >&2
        exit 1
    fi
done

mkdir -p "${CI_BASE_BUILD_DIR}/coq-failing/_build_ci/"
args=("-y" "$FILE" "${BUG_FILE}" "${TMP_FILE}" --no-deps --inline-user-contrib --coqc="${FAILING_COQC}" --coqtop="${FAILING_COQTOP}" --coq_makefile="${FAILING_COQ_MAKEFILE}" --base-dir="${CI_BASE_BUILD_DIR}/coq-failing/_build_ci/" -Q "${BUG_TMP_DIR}" Top)
while IFS= read -r line; do
    args+=("$line")
done <<< "${FAILING_ARGS}"
if [ "${PASSING_COQC}" != "${FAILING_COQC}" ]; then
    # are running with two versions
    mkdir -p "${CI_BASE_BUILD_DIR}/coq-passing/_build_ci/"
    args+=(--passing-coqc="${PASSING_COQC}" --passing-base-dir="${CI_BASE_BUILD_DIR}/coq-passing/_build_ci/")
    while IFS= read -r line; do
        args+=("$line")
    done <<< "${PASSING_ARGS}"
fi
args+=(-l - "$DIR/bug.log")

# allow coqbot.sh to set extra_args
if [ -f "$DIR/extra-args.sh" ]; then
    source "$DIR/extra-args.sh"
fi

pwd
"$PYTHON" "$DIR/coq-tools/find-bug.py" "${args[@]}" "${extra_args[@]}" || exit $?
