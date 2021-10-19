#!/usr/bin/env bash
# Should be invoked from run.sh

set -e -o pipefail

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

source "$DIR/coqbot-config.sh"

set -x

if ! command -v sudo &> /dev/null; then
    echo '::group::install sudo'
    su -c 'apt-get update -y'
    su -c 'apt-get install -y sudo'
    echo '::endgroup::'
fi

sudo chmod a+rw .

git clone https://github.com/JasonGross/coq-tools.git

if [ -z "${PYTHON}" ]; then
    PYTHON="$(which python3 || which python)"
fi

echo '::group::install general dependencies'
sudo apt-get update -y
sudo apt-get install -y wget curl
opam update -y
eval $(opam env)
echo '::endgroup::'

# Kludge for quicker running locally
if [ ! -f "$DIR/build.log.orig" ]; then
    if [ "${RUN_KIND}" == "coqbot-ci" ]; then
        source "$DIR/coqbot-ci.sh" 2>&1 | tee "${BUILD_LOG}"
    else
        echo '::group::wrap binaries'
        for i in coqc coqtop; do
            pushd "$(dirname "$(which "$i")")"
            wrap_file "$i"
            popd
        done
        echo '::endgroup::'

        source "$DIR/coqbot.sh" 2>&1 | tee "${BUILD_LOG}" || true
    fi
else
    cp -f "$DIR/build.log.orig" "${BUILD_LOG}"
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
    skip_next=no
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
        elif [ "${skip_next}" == "yes" ]; then
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
                -batch|-time|-noglob)
                    # we already transform coqtop to coqc as necessary, so we can safely ignore -batch
                    #
                    # we don't need to pass in -time, as it's purely informative and makes logs longer
                    #
                    # we must not pass in -noglob, because we rely on generated glob files
                    ;;
                -o|-dump-glob)
                    # We don't pass along -o/-dump-glob arguments,
                    # because we're not outputting to the same
                    # .vo/.glob files
                    skip_next=yes
                    ;;
                *)
                    echo "${prefixed_arg}=$i"
                    ;;
            esac
        fi
        cur_arg=""
    done
}

function coqpath_to_args() {
    local IFS=:
    for i in $1; do
        echo "-I"
        echo "$i"
        while IFS= read -r subdir; do
            if [ -d "$i/$subdir" ]; then
                echo "-Q"
                echo "$i/$subdir"
                echo "$subdir"
            fi
        done < <(ls "$i")
    done
}

echo '::group::process logs'

set +o pipefail

FILE="$(tac "${BUILD_LOG}" | grep --max-count=1 -A 1 '^Error' | grep '^File "[^"]*", line [0-9]*, characters [0-9-]*:' | grep -o '^File "[^"]*' | sed 's/^File "//g')"
EXEC_AND_PATH_AND_PWD="$(tac "${BUILD_LOG}" | grep -A 3 -F "$FILE" | grep --max-count=1 -A 3 'MINIMIZER_DEBUG: exec')"
EXEC="$(echo "${EXEC_AND_PATH_AND_PWD}" | grep 'MINIMIZER_DEBUG: exec' | grep -o 'exec:\? .*' | sed 's/^exec:\? //g')"
COQPATH="$(echo "${EXEC_AND_PATH_AND_PWD}" | grep 'MINIMIZER_DEBUG: coqpath' | grep -o 'COQPATH=.*' | sed 's/^COQPATH=//g')"
EXEC_PWD="$(echo "${EXEC_AND_PATH_AND_PWD}" | grep 'MINIMIZER_DEBUG: pwd' | grep -o 'PWD=.*' | sed 's/^PWD=//g')"

function split_args_to_lines() {
    for arg in "$@"; do
        echo "$arg"
    done
}
export -f split_args_to_lines

FAILING_COQPATH="$COQPATH"
# some people (like Iris) like to use `coqtop -batch -lv` or similar to process a .v file, so we replace coqtop with coqc
# Use bash -c to unescape the bash escapes in EXEC
FAILING_COQC="$(bash -c "split_args_to_lines ${EXEC}" | head -1 | sed 's,bin/coqtop,bin/coqc,g')"

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

FAILING_ARGS="$( cd "${EXEC_PWD}" && ( (bash -c "split_args_to_lines ${EXEC}" | tail -n +2; coqpath_to_args "${FAILING_COQPATH}") | process_args "${NONPASSING_PREFIX}" "${FILE}") )"
PASSING_ARGS="$( cd "${EXEC_PWD}" && ( (bash -c "split_args_to_lines ${EXEC}" | tail -n +2 | sed "s,\(${CI_BASE_BUILD_DIR}\)/coq-failing/,\\1/coq-passing/,g"; coqpath_to_args "${PASSING_COQPATH}") | process_args passing "${FILE}") )"
ABS_FILE="$(cd "${EXEC_PWD}" && readlink -f "${FILE}")"

set +o pipefail

echo -n "${ABS_FILE}" > "$DIR/filename"

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
args=("-y")
if [ -f "${FINAL_BUG_FILE}" ]; then # resume minimization from the final bug file
    echo "Resuming minimization from ${FINAL_BUG_FILE}..."
    echo "Skipping checking of log file..."
    cp -f "${FINAL_BUG_FILE}" "${BUG_FILE}" # attempt to kludge around https://github.com/JasonGross/coq-tools/issues/42 by placing the bug file in a directory that is not a direct ancestor of the library
    args+=("${BUG_FILE}" "${BUG_FILE}" "${TMP_FILE}")
else
    args+=(    "${ABS_FILE}" "${BUG_FILE}" "${TMP_FILE}" --error-log="${BUILD_LOG}")
fi
args+=(--no-deps --ignore-coq-prog-args --inline-user-contrib --coqc="${FAILING_COQC}" --coqtop="${FAILING_COQTOP}" --coq_makefile="${FAILING_COQ_MAKEFILE}" --base-dir="${CI_BASE_BUILD_DIR}/coq-failing/_build_ci/" -Q "${BUG_TMP_DIR}" Top)
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

echo '::endgroup::'

eval $(opam env)

pwd
# remove the .glob file to force the bug finder to remake it with passing coqc
rm -f "${FILE/.v/.glob}" "${FILE/.v/.vo}"
# we want to have ${TIMEDOUT_STAMP_FILE} exist iff we were killed by
# timeout, so we create it when we're invoked with a timeout, and then
# remove it on both successful and unsuccessful completion of the bug
# finder script
if [ ! -z "$TIMEOUT" ]; then
    touch "${TIMEDOUT_STAMP_FILE}"
fi
RV=0
# Even with set -ex, don't interrupt the printf
echo "$(printf "%s %q " "::warning::Running command" "$PYTHON" "$DIR/coq-tools/find-bug.py" "${args[@]}" "${extra_args[@]}")"
"$PYTHON" "$DIR/coq-tools/find-bug.py" "${args[@]}" "${extra_args[@]}" || RV=$?
rm -f "${TIMEDOUT_STAMP_FILE}"
exit $RV
