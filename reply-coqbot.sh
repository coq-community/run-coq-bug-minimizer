#!/usr/bin/env bash
# USAGE: $0 ID ORIG_FILENAME MINIMIZED_FILE_NAME TEMP_FILE_NAME BUILD_LOG_NAME MINIMIZATION_LOG_NAME
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

. "$DIR/coqbot-config.sh"

set -x

id="$1"
comment_contents="Minimized File $2 (full log [on GitHub Actions](${GITHUB_WORKFLOW_URL}))"
if [ ! -z "${SURVEY_URL}" ] && [ ! -z "${SURVEY_PR_URL_PARAMETER}" ] && [ ! -z "${ISSUE_NUMBER}" ] && [ ! -z "$DIR/early-feedback.md" ]; then
    comment_contents+="${nl}${nl}$(cat "$DIR/early-feedback.md" | sed "s>@SURVEY_URL@>${SURVEY_URL}?${SURVEY_PR_URL_PARAMETER}=${ISSUE_NUMBER}>g")"
fi
comment_contents+="$(print_file head "$(( ${GITHUB_MAX_CHAR_COUNT} / 2 ))" "Minimized Coq File" " (consider adding this file to the test-suite)" "${start_coq_code}" "$3" "${end_code}")"
comment_contents+="$(print_file head "$(( ${GITHUB_MAX_CHAR_COUNT} / 8 ))" "Intermediate Coq File (useful for debugging if minimization did not go as far as you wanted)" "" "${start_coq_code}" "$4" "${end_code}")"
comment_contents+="$(print_file tail "$(( ${GITHUB_MAX_CHAR_COUNT} / 8 ))" "Build Log (contains the Coq error message)" "" "${start_code}" "$5" "${end_code}")"
comment_contents+="$(print_file tail "$(( ${GITHUB_MAX_CHAR_COUNT} / 8 ))" "Minimization Log" "" "${start_code}" "$6" "${end_code}")"
comment_contents+="${nl}${nl}$(cat "$DIR/feedback.md")"

file="$(mktemp)"
cat > "$file" <<EOF
${id}${nl}${comment_contents}
EOF

if [ ! -z "${COQBOT_URL}" ]; then
    date
    curl -X POST --data-binary "@${file}" "${COQBOT_URL}"
else
    echo curl -X POST --data-binary "@${file}"
    echo cat "$file"
    cat "$file"
fi

rm "$file"
