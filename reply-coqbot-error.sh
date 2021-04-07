#!/usr/bin/env bash
# USAGE: $0 ID FILENAME ERROR_LOG_FILENAME

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

. "$DIR/coqbot-config.sh"

set -x

id="$1"
comment_contents="Error: Could not minimize file $2 (full log [on GitHub Actions](${GITHUB_WORKFLOW_URL}))"
comment_contents+="$(print_file "build log" "${start_code}" "$3" "${end_code}")"
comment_contents+="$(print_file "minimizer log" "${start_code}" "$4" "${end_code}")"
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
