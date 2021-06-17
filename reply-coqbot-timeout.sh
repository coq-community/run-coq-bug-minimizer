#!/usr/bin/env bash
# USAGE: $0 ID ORIG_FILENAME MINIMIZED_FILE_NAME TEMP_FILE_NAME BUILD_LOG_NAME MINIMIZATION_LOG_NAME
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

. "$DIR/coqbot-config.sh"

set -x

bash "$DIR/reply-coqbot.sh" "$@"

id="$1"
bug_file_contents="$(cat "$3")"
commit_message="$(echo -n "$(git log -1 --pretty=%B)" | tr '\n' '\t')"

file="$(mktemp)"
cat > "$file" <<EOF
${id}
${RESUMPTION_ARGS}
${bug_file_contents}
EOF

if [ ! -z "${COQBOT_RESUME_MINIMIZATION_URL}" ]; then
    curl -X POST --data-binary "@${file}" "${COQBOT_RESUME_MINIMIZATION_URL}"
else
    echo curl -X POST --data-binary "@${file}"
    echo cat "$file"
    cat "$file"
fi

rm "$file"
