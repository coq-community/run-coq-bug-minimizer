#!/usr/bin/env bash

function usage() {
    printf 'USAGE: %q FILE_NAME ARTIFACT_ID OUTCOME\n' "$0"
    # outcome should be success, failure, cancelled, or skipped, cf https://stackoverflow.com/a/70549615/377022
    exit 1
}

if [ "$#" -ne 3 ]; then
    usage
fi

filename="$1"
artifact_id="$2"
outcome="$3"
if [ "${outcome}" == "success" ] && [ ! -z "${artifact_id}" ]; then
    printf '%s' "${GITHUB_API_URL}/repos/${GITHUB_REPOSITORY}/actions/artifacts/${artifact_id}/zip" | tee "${filename}.api.url"
    echo
    printf '%s' "${GITHUB_SERVER_URL}/${GITHUB_REPOSITORY}/actions/runs/${GITHUB_RUN_ID}/artifacts/${artifact_id}" | tee "${filename}.url"
    echo
fi
