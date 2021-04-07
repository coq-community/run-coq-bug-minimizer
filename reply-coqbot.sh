#!/usr/bin/env bash
# USAGE: $0 ID ORIG_FILENAME MINIMIZED_FILE_NAME BUILD_LOG_NAME MINIMIZATION_LOG_NAME
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

. "$DIR/coqbot-config.sh"

set -x

id="$1"
comment_contents="Minimized File $2 (full log [on GitHub Actions](${GITHUB_WORKFLOW_URL}))"
comment_contents+="$(print_file "Minimized Coq File" "${start_coq_code}" "$3" "${end_code}")"
comment_contents+="$(print_file "Intermediate Coq File (useful for debugging if minimization did not go as far as you wanted)" "${start_coq_code}" "$4" "${end_code}")"
comment_contents+="$(print_file "Build Log" "${start_code}" "$5" "${end_code}")"
comment_contents+="$(print_file "Minimization Log" "${start_code}" "$6" "${end_code}")"
comment_contents+="${nl}${nl}$(cat "$DIR/feedback.md")"

file="$(mktemp)"
cat > "$file" <<EOF
${id}${nl}${comment_contents}
EOF

if [ ! -z "${COQBOT_URL}" ]; then
    curl -X POST --data-binary "@${file}" "${COQBOT_URL}"
else
    echo curl -X POST --data-binary "@${file}"
    echo cat "$file"
    cat "$file"
fi

rm "$file"
