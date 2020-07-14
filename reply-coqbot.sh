#!/usr/bin/env bash
# USAGE: $0 ID ORIG_FILENAME MINIMIZED_FILE_NAME BUILD_LOG_NAME MINIMIZATION_LOG_NAME
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

. "$DIR/coqbot-config.sh"

id="$1"
comment_contents="Minimized File $2"
comment_contents+="${nl}${nl}<details><summary>Minimized Coq File</summary>${nl}${nl}${start_coq_code}$(cat "$3")${end_code}</details>"
comment_contents+="${nl}${nl}<details><summary>Build Log</summary>${nl}${nl}${start_code}$(cat "$4")${end_code}</details>"
comment_contents+="${nl}${nl}<details><summary>Minimization Log</summary>${nl}${nl}${start_code}$(cat "$5")${end_code}</details>"

if [ ! -z "${COQBOT_URL}" ]; then
    curl -X POST --data-binary "${id}${nl}${comment_contents}" "${COQBOT_URL}"
else
    echo curl -X POST --data-binary "${id}${nl}${comment_contents}"
fi
