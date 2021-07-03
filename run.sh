#!/usr/bin/env bash

set -o pipefail

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

source "$DIR/coqbot-config.sh"

rm -f "${TIMEDOUT_STAMP_FILE}"

function cleanup() {
    echo '::group::cleanup'
    cp -f "${BUG_FILE}" "${FINAL_BUG_FILE}" || RC=$?
    cp -f "${TMP_FILE}" "${FINAL_TMP_FILE}" || touch "${FINAL_TMP_FILE}"
    mkdir -p "${FINAL_TMP_FOLDER}"
    find /tmp | xargs ls -la
    cp -a /tmp "${FINAL_TMP_FOLDER}" || true
    chmod -R a+rw "${FINAL_TMP_FOLDER}" || true
    find "${FINAL_TMP_FOLDER}" | xargs ls -la
    STAMP="$(cat "$DIR/coqbot-request-stamp")"
    touch "$DIR/filename"
    FILE="$(cat "$DIR/filename")"
    EXTRA_DESCRIPTION=""
    if [ ! -z "${CI_TARGET}" ]; then
        EXTRA_DESCRIPTION=" (from ${CI_TARGET})"
    fi
    if [ -f "${TIMEDOUT_STAMP_FILE}" ]; then # timeout!
        EXTRA_DESCRIPTION="${EXTRA_DESCRIPTION} (interrupted by timeout"
        if [ ! -z "${COQBOT_RESUME_MINIMIZATION_URL}" ]; then
            EXTRA_DESCRIPTION="${EXTRA_DESCRIPTION}, being automatically continued"
        fi
        EXTRA_DESCRIPTION="${EXTRA_DESCRIPTION})"
    fi
    if [ -f "${FINAL_BUG_FILE}" ]; then
        touch "${BUILD_LOG}" "${BUG_LOG}"
        if [ -f "${TIMEDOUT_STAMP_FILE}" ]; then # timeout!
            bash "$DIR/reply-coqbot-timeout.sh" "$STAMP" "${FILE}${EXTRA_DESCRIPTION}" "${FINAL_BUG_FILE}" "${FINAL_TMP_FILE}" "${BUILD_LOG}" "${BUG_LOG}"
        else
            bash "$DIR/reply-coqbot.sh" "$STAMP" "${FILE}${EXTRA_DESCRIPTION}" "${FINAL_BUG_FILE}" "${FINAL_TMP_FILE}" "${BUILD_LOG}" "${BUG_LOG}"
        fi
    else
        touch "${BUILD_LOG}" "${BUG_LOG}"
        bash "$DIR/reply-coqbot-error.sh" "$STAMP" "${FILE}${EXTRA_DESCRIPTION}" "${BUILD_LOG}" "${BUG_LOG}"
    fi
    echo '::endgroup::'
    exit $RC
}

trap cleanup SIGINT SIGKILL EXIT

echo "::remove-matcher owner=coq-problem-matcher::"
echo "::add-matcher::$DIR/coq.json"

set -x

if [ -z "$TIMEOUT" ]; then
    "$DIR/run-script.sh" || exit $?
else
    timeout "$TIMEOUT" "$DIR/run-script.sh" || exit $?
fi
