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
    touch "${METADATA_FILE}"
    STAMP="$(cat "$DIR/coqbot-request-stamp")"
    echo "STAMP=${STAMP}" >> "${METADATA_FILE}"
    touch "$DIR/filename"
    FILE="$(cat "$DIR/filename")"
    echo "FILE=${FILE}" >> "${METADATA_FILE}"
    EXTRA_DESCRIPTION=""
    echo "CI_TARGET=${CI_TARGET}" >> "${METADATA_FILE}"
    if [ ! -z "${CI_TARGET}" ]; then
        EXTRA_DESCRIPTION=" (from ${CI_TARGET})"
    fi
    if [ -f "${TIMEDOUT_STAMP_FILE}" ]; then # timeout!
        EXTRA_DESCRIPTION="${EXTRA_DESCRIPTION} (interrupted by timeout"
        if [ ! -z "${COQBOT_RESUME_MINIMIZATION_URL}" ]; then
            echo "COQBOT_RESUME_MINIMIZATION_URL=${COQBOT_RESUME_MINIMIZATION_URL}" >> "${METADATA_FILE}"
            EXTRA_DESCRIPTION="${EXTRA_DESCRIPTION}, being automatically continued"
        fi
        EXTRA_DESCRIPTION="${EXTRA_DESCRIPTION})"
    fi
    if [ -f "${FINAL_BUG_FILE}" ]; then
        touch "${BUILD_LOG}" "${BACKUP_BUG_LOG}"
        if [ ! -f "${BUG_LOG}" ] || ! grep -q '[^[:space:]]' < "${BUG_LOG}"; then
            cp -f "${BACKUP_BUG_LOG}" "${BUG_LOG}"
        fi
        if [ -f "${TIMEDOUT_STAMP_FILE}" ]; then # timeout!
            echo "TIMEDOUT=1" >> "${METADATA_FILE}"
            echo "RESUMPTION_ARGS=${RESUMPTION_ARGS}" >> "${METADATA_FILE}"
            bash "$DIR/reply-coqbot-timeout.sh" "$STAMP" "${FILE}${EXTRA_DESCRIPTION}" "${FINAL_BUG_FILE}" "${FINAL_TMP_FILE}" "${BUILD_LOG}" "${BUG_LOG}"
        else
            bash "$DIR/reply-coqbot.sh" "$STAMP" "${FILE}${EXTRA_DESCRIPTION}" "${FINAL_BUG_FILE}" "${FINAL_TMP_FILE}" "${BUILD_LOG}" "${BUG_LOG}"
        fi
    else
        touch "${BUILD_LOG}" "${BUG_LOG}"
        echo "ERROR=1" >> "${METADATA_FILE}"
        bash "$DIR/reply-coqbot-error.sh" "$STAMP" "${FILE}${EXTRA_DESCRIPTION}" "${BUILD_LOG}" "${BUG_LOG}"
    fi
    echo '::endgroup::'
    exit $RC
}

trap cleanup SIGINT SIGKILL EXIT

echo "::remove-matcher owner=coq-problem-matcher::"
echo "::add-matcher::$DIR/coq.json"

set -x

source "$DIR/ensure-sudo.sh"
# we pipe each step to the bug log in case it fails

sudo chmod a+rw .

if [ -z "$TIMEOUT" ]; then
    "$DIR/run-script.sh" 2>&1 | tee "${BACKUP_BUG_LOG}" || exit $?
else
    timeout "$TIMEOUT" "$DIR/run-script.sh" 2>&1 | tee "${BACKUP_BUG_LOG}" || exit $?
fi
