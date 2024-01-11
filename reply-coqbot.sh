#!/usr/bin/env bash
# USAGE: $0 ID ORIG_FILENAME MINIMIZED_FILE_NAME TEMP_FILE_NAME BUILD_LOG_NAME MINIMIZATION_LOG_NAME
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

. "$DIR/coqbot-config.sh"

set -x

id="$1"
comment_contents="Minimized File $2 (full log [on GitHub Actions](${GITHUB_WORKFLOW_URL})$(if_wrap_with_url "${VERBOSE_BUG_LOG}" " - " "verbose log" "" ""))"
if [ ! -z "${SURVEY_URL}" ] && [ ! -z "${SURVEY_PR_URL_PARAMETER}" ] && [ ! -z "${ISSUE_NUMBER}" ] && [ ! -z "$DIR/early-feedback.md" ] && [ ! -f "${TIMEDOUT_STAMP_FILE}" ]; then
    comment_contents+="${nl}${nl}$(cat "$DIR/early-feedback.md" | sed "s>@SURVEY_URL@>${SURVEY_URL}?${SURVEY_PR_URL_PARAMETER}=${ISSUE_NUMBER}>g")"
fi
uninlinable_modules="$(grep '^\s*Modules that could not be inlined:' "$3" | sed 's/^\s*Modules that could not be inlined:\s*//g')"
if [ ! -z "${uninlinable_modules}" ]; then
    min_descr=":star: :building_construction: Partially Minimized Coq File (could not inline ${uninlinable_modules})"
    add_to_test_suite=""
elif [ -f "${TIMEDOUT_STAMP_FILE}" ]; then # timeout!
    min_descr=":star: :stopwatch: Partially Minimized Coq File (timeout)"
    add_to_test_suite=""
else
    min_descr=":star2: Minimized Coq File"
    add_to_test_suite=" (consider adding this file to the test-suite)"
fi
comment_contents+="$(print_file head-tail "$(( ${GITHUB_MAX_CHAR_COUNT} / 2 ))" "${min_descr}" "${add_to_test_suite}" "${start_coq_code}" "$3" "${end_code}")"
comment_contents+="$(print_file head "$(( 3 * ${GITHUB_MAX_CHAR_COUNT} / 32 ))" ":hammer_and_wrench: Intermediate Coq File (useful for debugging if minimization did not go as far as you wanted)" "" "${start_coq_code}" "$4" "${end_code}")"
comment_contents+="$(print_file tail "$(( 1 * ${GITHUB_MAX_CHAR_COUNT} / 32 ))" ":hammer_and_wrench: :scroll: Intermediate Coq File log (useful for debugging if minimization did not go as far as you wanted)" "" "${start_coq_code}" "$5" "${end_code}")"
comment_contents+="$(print_file tail "$(( ${GITHUB_MAX_CHAR_COUNT} / 8 ))" ":scroll: Build Log (contains the Coq error message)" "" "${start_code}" "$6" "${end_code}")"
comment_contents+="$(print_file tail "$(( ${GITHUB_MAX_CHAR_COUNT} / 8 ))" ":scroll: :mag_right: Minimization Log" "" "${start_code}" "$7" "${end_code}")"
comment_contents+="${nl}${nl}$(cat "$DIR/feedback.md")"
if [ ! -z "${uninlinable_modules}" ]; then
    comment_contents+="${nl}${nl}cc @JasonGross"
fi

file="$(mktemp)"
cat > "$file" <<EOF
${id}${nl}${comment_contents}
EOF

echo cat "$file"
cat "$file"

if [ ! -z "${COQBOT_URL}" ]; then
    date -u
    curl -X POST --data-binary "@${file}" "${COQBOT_URL}"
else
    echo curl -X POST --data-binary "@${file}"
fi

rm "$file"
