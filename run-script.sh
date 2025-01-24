#!/usr/bin/env bash
# Should be invoked from run.sh

set -e -o pipefail

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

source "$DIR/coqbot-config.sh"

set -x

git config --global --add safe.directory /github/workspace
git config --global --add safe.directory "$(pwd)"

git clone https://github.com/JasonGross/coq-tools.git

if [ -z "${PYTHON}" ]; then
    PYTHON="$(which python3 || which python)"
fi

printf '::group::install general dependencies\n'
sudo apt-get update -y
sudo apt-get install -y wget curl
opam update -y
eval $(opam env)
printf '::endgroup::\n'

printf '::group::opam list\n'
opam list
printf '::endgroup::\n'

# Kludge for quicker running locally
if [ ! -f "$DIR/build.log.orig" ]; then
    if [ "${RUN_KIND}" == "coqbot-ci" ]; then
        source "$DIR/coqbot-ci.sh" 2>&1 | tee "${BUILD_LOG}"
    else
        printf '::group::wrap binaries\n'
        wrap_opam_and_files coqc coqtop rocq
        printf '::endgroup::\n'

        {
            ocamlc -config
            coqc --config
            coqc --version
            true | coqtop

            source "$DIR/coqbot.sh"
            # use sed to handle opam output
        } 2>&1 | sed 's/^# //g' | tee "${BUILD_LOG}" || true
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
    coqlib=""
    if [ ! -z "$2" ]; then
        coqlib="$2"
    fi
    known_v_file="$2"
    next_is_coqlib=no
    next_is_known=no
    next_next_is_known=no
    skip_next=no
    prev_load=""
    found_known_v_file=no
    while read i; do
        >&2 printf "process_args: processing (%q)\n" "$i"
        if [[ "$i" == *".v" ]] && [ "$(readlink -f "${known_v_file}")" == "$(readlink -f "$i")" ]; then
            found_known_v_file=yes
        fi
        if [ ! -z "${prev_load}" ]; then
            if [ "${found_known_v_file}" == "yes" ]; then
                : # we want to skip over loading the file which is buggy, and any loads which come after it, but we want to load files that come before it
            else
                printf "%s\n" "${prev_load}"
                printf "%s=%s\n" "${prefixed_arg}" "$i"
            fi
            prev_load=""
            next_is_known="${next_next_is_known}"
            next_next_is_known=no
            next_is_coqlib=no
        elif [ "${skip_next}" == "yes" ]; then
            next_is_known="${next_next_is_known}"
            next_next_is_known=no
            skip_next=no
            next_is_coqlib=no
        elif [ "${next_is_known}" == "yes" ]; then
            printf "%s\n" "$i"
            next_is_known="${next_next_is_known}"
            next_next_is_known=no
            next_is_coqlib=no
        elif [ "${next_is_coqlib}" == "yes" ]; then
            printf "%s=%s\n" "${prefixed_arg}" "$i"
            coqlib=""
            next_is_coqlib=no
        elif [[ "$i" == *".v" ]]; then
            :
        else
            case "$i" in
                -R|-Q)
                    printf "%s%s\n" "${passing_prefix}" "${i}"
                    next_is_known=yes
                    next_next_is_known=yes
                    ;;
                -I)
                    printf "%s%s\n" "${passing_prefix}" "${i}"
                    next_is_known=yes
                    ;;
                -arg)
                    printf "%s\n" "${prefixed_arg}"
                    next_is_known=yes
                    ;;
                -l|-lv|-load-vernac-source|-load-vernac-source-verbose)
                    prev_load="${prefixed_arg}=$i"
                    next_is_known=yes
                    ;;
                -batch|-compile|-time|-noglob)
                    # we already transform coqtop to coqc as necessary, so we can safely ignore -batch and -compile
                    #
                    # we don't need to pass in -time, as it's purely informative and makes logs longer
                    #
                    # we must not pass in -noglob, because we rely on generated glob files
                    ;;
                -o|-dump-glob|-time-file)
                    # We don't pass along -o/-dump-glob/-time-file arguments,
                    # because we're not outputting to the same
                    # .vo/.glob/.timing files
                    skip_next=yes
                    ;;
                -coqlib)
                    printf "%s=%s\n" "${prefixed_arg}" "$i"
                    next_is_coqlib=yes
                    ;;
                *)
                    printf "%s=%s\n" "${prefixed_arg}" "$i"
                    ;;
            esac
        fi
        cur_arg=""
    done
    if [ ! -z "${coqlib}" ]; then
        printf "%s=%s\n" "${prefixed_arg}" "-coqlib"
        printf "%s=%s\n" "${prefixed_arg}" "${coqlib}"
    fi
}

function coqpath_to_args() {
    cd "$1"
    local IFS=:
    for i in $2; do
        printf "%s\n" "-I"
        (cd "$i" && pwd)
        while IFS= read -r subdir; do
            if [ -d "$i/$subdir" ]; then
                printf "%s\n" "-Q"
                (cd "$i/$subdir" && pwd)
                printf "%s\n" "$subdir"
            fi
        done < <(ls "$i")
    done
}

function split_args_to_lines() {
    for arg in "$@"; do
        printf "%s\n" "$arg"
    done
}
export -f split_args_to_lines

printf '::group::process logs\n'

set +o pipefail

FILE="$(tac "${BUILD_LOG}" | grep --max-count=1 -A 1 '^Error' | grep '^File "[^"]*", line [0-9]*, characters [0-9-]*:' | grep -o '^File "[^"]*' | sed 's/^File "//g; s,^\./\+,,g')"
DEBUG_PREFIX="$(tac "${BUILD_LOG}" | grep -A 1 -F "$FILE" | grep --max-count=1 -o 'MINIMIZER_DEBUG: info: .*' | sed 's/^MINIMIZER_DEBUG: info: //g')"
EXEC="$(cat "${DEBUG_PREFIX}.exec" | sed "s,${COQ_CI_BASE_BUILD_DIR},${CI_BASE_BUILD_DIR}/coq-failing,g")"
COQPATH="$(cat "${DEBUG_PREFIX}.coqpath" | sed "s,${COQ_CI_BASE_BUILD_DIR},${CI_BASE_BUILD_DIR}/coq-failing,g")"
EXEC_PWD="$(cat "${DEBUG_PREFIX}.pwd" | sed "s,${COQ_CI_BASE_BUILD_DIR},${CI_BASE_BUILD_DIR}/coq-failing,g")"
COQLIB="$(cat "${DEBUG_PREFIX}.config" | sed "s,${COQ_CI_BASE_BUILD_DIR},${CI_BASE_BUILD_DIR}/coq-failing,g" | grep '^COQLIB=' | sed 's/^COQLIB=//g')"

FAILING_COQPATH="$COQPATH"
# some people (like Iris) like to use `coqtop -batch -lv` or similar to process a .v file, so we replace coqtop with coqc
# Use bash -c to unescape the bash escapes in EXEC
FAILING_COQC="$(bash -c "split_args_to_lines ${EXEC}" | head -1 | sed 's,bin/coqtop,bin/coqc,g; s,bin/rocq top,bin/rocq c,g')"
FAILING_EXEC_PWD="${EXEC_PWD}"

FAILING_COQTOP="$(printf "%s" "$FAILING_COQC" | sed 's,bin/coqc,bin/coqtop,g; s,bin/rocq top,bin/rocq c,g')"

PASSING_COQPATH="$(printf "%s" "$COQPATH" | sed "s,\(${CI_BASE_BUILD_DIR}\)/coq-failing/,\\1/coq-passing/,g")"
PASSING_COQC="$(printf '%s\n' ${EXEC} | head -1 | sed "s,\(${CI_BASE_BUILD_DIR}\)/coq-failing/,\\1/coq-passing/,g" | sed 's,bin/coqtop,bin/coqc,g; s,bin/rocq top,bin/rocq c,g')"
PASSING_EXEC_PWD="$(printf "%s" "${EXEC_PWD}" | sed "s,\(${CI_BASE_BUILD_DIR}\)/coq-failing/,\\1/coq-passing/,g")"
PASSING_COQLIB="$(printf "%s" "${COQLIB}" | sed "s,\(${CI_BASE_BUILD_DIR}\)/coq-failing/,\\1/coq-passing/,g")"

PASSING_COQTOP="$(printf "%s" "$PASSING_COQC" | sed 's,bin/coqc,bin/coqtop,g; s,bin/rocq top,bin/rocq c,g')"
PASSING_COQ_MAKEFILE="$(cd "$(dirname "${PASSING_COQC}")" && readlink -f coq_makefile)"
PASSING_COQDEP="$(cd "$(dirname "${PASSING_COQC}")" && readlink -f coqdep)"

if [ "${PASSING_COQC}" != "${FAILING_COQC}" ]; then
    # we are running with two versions
    NONPASSING_PREFIX="nonpassing"
else
    # we are running only with one version of coqc, so the minimizer doesn't support --nonpassing prefixes
    NONPASSING_PREFIX=""
fi

argsfile="$(mktemp)"
{ cd "${EXEC_PWD}" && { { bash -c "split_args_to_lines ${EXEC}" | tail -n +2; coqpath_to_args "${FAILING_EXEC_PWD}" "${FAILING_COQPATH}"; } | process_args "${NONPASSING_PREFIX}" "${FILE}" "${FAILING_COQLIB}"; }; } > "${argsfile}"
mapfile -t FAILING_ARGS < "${argsfile}"
{ cd "${EXEC_PWD}" && { { bash -c "split_args_to_lines ${EXEC}" | tail -n +2 | sed "s,\(${CI_BASE_BUILD_DIR}\)/coq-failing/,\\1/coq-passing/,g"; coqpath_to_args "${PASSING_EXEC_PWD}" "${PASSING_COQPATH}"; } | process_args passing "${FILE}" "${PASSING_COQLIB}"; }; } > "${argsfile}"
mapfile -t PASSING_ARGS < "${argsfile}"
ABS_FILE="$(cd "${EXEC_PWD}" && readlink -f "${FILE}")"

set +o pipefail

printf "%s" "${ABS_FILE}" > "$DIR/filename"

mkdir -p "$(dirname "${BUG_FILE}")"
mkdir -p "$(dirname "${TMP_FILE}")"
mkdir -p "$(dirname "${TMP_LOG}")"

cd "$(dirname "${BUG_FILE}")"

for VAR in FAILING_COQC FAILING_COQTOP PASSING_COQC PASSING_COQ_MAKEFILE PASSING_COQDEP; do
    if [ ! -x "${!VAR}" ]; then
        printf "Error: Could not find %s ('%s')\n" "${VAR}" "${!VAR}" | tee -a "${BUG_LOG}" "${VERBOSE_BUG_LOG}" >&2
        printf "Files in '%s':\n" "$(dirname ${!VAR})" | tee -a "${BUG_LOG}" "${VERBOSE_BUG_LOG}" >&2
        find "$(dirname ${!VAR})" | tee -a "${BUG_LOG}" "${VERBOSE_BUG_LOG}" >&2
        exit 1
    fi
done

mkdir -p "${CI_BASE_BUILD_DIR}/coq-failing/_build_ci/"
args=("-y")
if [ -f "${FINAL_BUG_FILE}" ]; then # resume minimization from the final bug file
    printf "Resuming minimization from %s...\n" "${FINAL_BUG_FILE}"
    printf "Skipping checking of log file...\n"
    cp -f "${FINAL_BUG_FILE}" "${BUG_FILE}" # attempt to kludge around https://github.com/JasonGross/coq-tools/issues/42 by placing the bug file in a directory that is not a direct ancestor of the library
    args+=("${BUG_FILE}" "${BUG_FILE}" "${TMP_FILE}")
else
    args+=("${ABS_FILE}" "${BUG_FILE}" "${TMP_FILE}" --error-log="${BUILD_LOG}" --temp-file-log="${TMP_LOG}")
fi
args+=(--no-deps --ignore-coq-prog-args --inline-user-contrib --coqc="${FAILING_COQC}" --coqtop="${FAILING_COQTOP}" --coq_makefile="${PASSING_COQ_MAKEFILE}" --coqdep "${PASSING_COQDEP}" --base-dir="${FAILING_EXEC_PWD}" -Q "${BUG_TMP_DIR}" Top --verbose-include-failure-warning --verbose-include-failure-warning-prefix "::warning::" --verbose-include-failure-warning-newline "%0A")
printf '%s\n' "$(printf 'appending failing args: '; printf '%q ' "${FAILING_ARGS[@]}")"
args+=("${FAILING_ARGS[@]}")
if [ "${PASSING_COQC}" != "${FAILING_COQC}" ]; then
    # are running with two versions
    mkdir -p "${CI_BASE_BUILD_DIR}/coq-passing/_build_ci/"
    args+=(--passing-coqc="${PASSING_COQC}" --passing-coqtop="${PASSING_COQTOP}" --passing-base-dir="${EXEC_PWD}")
    printf '%s\n' "$(printf 'appending passing args: '; printf '%q ' "${FAILING_ARGS[@]}")"
    args+=("${PASSING_ARGS[@]}")
fi
args+=(-l - "${BUG_LOG}" --verbose-log-file "9999,${VERBOSE_BUG_LOG}")
args+=("${EXTRA_MINIMIZER_ARGUMENTS[@]}")

printf "args are: "
printf "%q " "${args[@]}"

printf '::endgroup::\n'

# remove problem matcher so we don't get duplicate spurious error matches
printf '::remove-matcher owner=coq-problem-matcher::\n'

pwd
# remove the .glob file to force the bug finder to remake it with passing coqc
rm -f "${FILE/.v/.glob}" "${FILE/.v/.vo}"

eval $(opam env)

# we want to have ${TIMEDOUT_STAMP_FILE} exist iff we were killed by
# timeout, so we create it when we're invoked with a timeout, and then
# remove it on both successful and unsuccessful completion of the bug
# finder script
if [ ! -z "$TIMEOUT" ]; then
    touch "${TIMEDOUT_STAMP_FILE}"
fi
RV=0
# Even with set -ex, don't interrupt the printf
printf "%s\n" "$(printf "%s" "::warning::Running command "; printf "%q " "$PYTHON" "$DIR/coq-tools/find-bug.py" "${args[@]}")"
"$PYTHON" "$DIR/coq-tools/find-bug.py" "${args[@]}" || RV=$?
rm -f "${TIMEDOUT_STAMP_FILE}"
exit $RV
