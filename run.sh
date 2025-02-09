#!/usr/bin/env bash

set -o pipefail

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

source "$DIR/coqbot-config.sh"

rm -f "${TIMEDOUT_STAMP_FILE}"

start_time="$(date +%s)"

function cleanup() {
    printf '::group::cleanup\n'
    end_time="$(date +%s)"
    duration=$((${PRIOR_DURATION} + end_time - start_time))
    printf '%d\n' "${duration}" > "${DURATION_FILE}"
    duration_str="$(pretty_seconds "${duration}")"
    cp -f "${BUG_FILE}" "${FINAL_BUG_FILE}" || RC=$?
    cp -f "${TMP_FILE}" "${FINAL_TMP_FILE}" || touch "${FINAL_TMP_FILE}"
    cp -f "${TMP_LOG}" "${FINAL_TMP_LOG}" || touch "${FINAL_TMP_LOG}"
    mkdir -p "${FINAL_TMP_FOLDER}"
    find /tmp | xargs ls -la
    cp -a /tmp "${FINAL_TMP_FOLDER}" || true
    chmod -R a+rw "${FINAL_TMP_FOLDER}" || true
    find "${FINAL_TMP_FOLDER}" | xargs ls -la
    touch "${METADATA_FILE}"
    STAMP="$(cat "$DIR/coqbot-request-stamp")"
    printf "STAMP=%s\n" "${STAMP}" >> "${METADATA_FILE}"
    touch "$DIR/filename"
    FILE="$(cat "$DIR/filename")"
    printf "FILE=%s\n" "${FILE}" >> "${METADATA_FILE}"
    EXTRA_DESCRIPTION=" in ${duration_str}"
    printf "CI_TARGET=%s\n" "${CI_TARGET}" >> "${METADATA_FILE}"
    if [ ! -z "${CI_TARGET}" ]; then
        EXTRA_DESCRIPTION="${EXTRA_DESCRIPTION} (from ${CI_TARGET})"
    fi
    if [ -f "${TIMEDOUT_STAMP_FILE}" ]; then # timeout!
        EXTRA_DESCRIPTION="${EXTRA_DESCRIPTION} (interrupted by timeout"
        if [ ! -z "${COQBOT_RESUME_MINIMIZATION_URL}" ]; then
            printf "COQBOT_RESUME_MINIMIZATION_URL=%s\n" "${COQBOT_RESUME_MINIMIZATION_URL}" >> "${METADATA_FILE}"
            EXTRA_DESCRIPTION="${EXTRA_DESCRIPTION}, being automatically continued"
        fi
        EXTRA_DESCRIPTION="${EXTRA_DESCRIPTION})"
    fi
    printf '%s\n\n' '#!/usr/bin/env bash' 'set -o pipefail' 'DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"' 'source "$DIR/coqbot-config.sh"' > "${CUSTOM_REPLY_COQBOT_FILE}"

    touch "${BUILD_LOG}" "${BACKUP_BUG_LOG}"
    if [ ! -f "${BUG_LOG}" ] || ! grep -q '[^[:space:]]' < "${BUG_LOG}"; then
        cp -f "${BACKUP_BUG_LOG}" "${BUG_LOG}"
    fi
    if [ -f "${FINAL_BUG_FILE}" ]; then
        if [ -f "${TIMEDOUT_STAMP_FILE}" ]; then # timeout!
            printf "TIMEDOUT=1\n" >> "${METADATA_FILE}"
            printf "RESUMPTION_ARGS=%s\n" "${RESUMPTION_ARGS}" >> "${METADATA_FILE}"
            printf '%q ' bash "$DIR/reply-coqbot-timeout.sh" "$STAMP" "${FILE}${EXTRA_DESCRIPTION}" "${FINAL_BUG_FILE}" "${FINAL_TMP_FILE}" "${FINAL_TMP_LOG}" "${BUILD_LOG}" "${BUG_LOG}" >> "${CUSTOM_REPLY_COQBOT_FILE}"
            printf '\n' >> "${CUSTOM_REPLY_COQBOT_FILE}"
        else
            printf '%q ' bash "$DIR/reply-coqbot.sh" "$STAMP" "${FILE}${EXTRA_DESCRIPTION}" "${FINAL_BUG_FILE}" "${FINAL_TMP_FILE}" "${FINAL_TMP_LOG}" "${BUILD_LOG}" "${BUG_LOG}" >> "${CUSTOM_REPLY_COQBOT_FILE}"
            printf '\n' >> "${CUSTOM_REPLY_COQBOT_FILE}"
        fi
    else
        touch "${BUILD_LOG}" "${BUG_LOG}"
        printf "ERROR=1\n" >> "${METADATA_FILE}"
        printf "%q " "bash" "$DIR/reply-coqbot-error.sh" "$STAMP" "${FILE}${EXTRA_DESCRIPTION}" "${BUILD_LOG}" "${BUG_LOG}" >> "${CUSTOM_REPLY_COQBOT_FILE}"
        printf '\n' >> "${CUSTOM_REPLY_COQBOT_FILE}"
    fi
    printf '::endgroup::\n'
    printf '::group::cat %q\n' "${CUSTOM_REPLY_COQBOT_FILE}"
    chmod a+rx "${CUSTOM_REPLY_COQBOT_FILE}"
    sed "s|${DIR}|"'${DIR}'"|g" -i "${CUSTOM_REPLY_COQBOT_FILE}"
    cat "${CUSTOM_REPLY_COQBOT_FILE}"
    printf '::endgroup::\n'
    exit $RC
}

trap cleanup SIGINT SIGKILL EXIT

printf "::remove-matcher owner=coq-problem-matcher::\n"
printf "::add-matcher::%s/coq.json\n" "$DIR"

set -x

source "$DIR/ensure-sudo.sh"
# we pipe each step to the bug log in case it fails

sudo chmod a+rw .

if [ -z "$TIMEOUT" ]; then
    "$DIR/run-script.sh" 2>&1 | tee "${BACKUP_BUG_LOG}" || exit $?
else
    timeout "$TIMEOUT" "$DIR/run-script.sh" 2>&1 | tee "${BACKUP_BUG_LOG}" || exit $?
fi
