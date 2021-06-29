#!/usr/bin/env bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

export nl=$'\n'
export backtick='`'
export start_code='```'"${nl}"
export start_coq_code='```coq'"${nl}"
export end_code="${nl}"'```'

. "$DIR/github-url.sh"

export BUG_TMP_DIR="$DIR/cwd"
export BUG_FILE="${BUG_TMP_DIR}/bug_01.v"
export TMP_FILE="${BUG_TMP_DIR}/tmp.v"
export FINAL_BUG_FILE="$DIR/bug.v" # must not change, since the deploy/artifact script looks for it
export FINAL_TMP_FILE="$DIR/tmp.v" # must not change, since the deploy/artifact script looks for it
export BUILD_LOG="$DIR/build.log" # must not change, since the deploy/artifact script looks for it
export BUG_LOG="$DIR/bug.log" # must not change, since the deploy/artifact script looks for it

export TIMEDOUT_STAMP_FILE="$DIR/timedout"

export COQBOT_URL="$(cat "$DIR/coqbot.url")"
export COQBOT_RESUME_MINIMIZATION_URL="$(cat "$DIR/coqbot.resume-minimization-url")"
export COMPILER="$(cat "$DIR/coqbot.compiler")"
export FAILING_ARTIFACT_URLS="$(echo $(cat "$DIR/coqbot.failing-artifact-urls"))"
export PASSING_ARTIFACT_URLS="$(echo $(cat "$DIR/coqbot.passing-artifact-urls"))"
export COQ_FAILING_SHA="$(echo $(cat "$DIR/coqbot.failing-sha"))"
export COQ_PASSING_SHA="$(echo $(cat "$DIR/coqbot.passing-sha"))"
export RESUMPTION_ARGS="$(cat "$DIR/coqbot.resumption-args")" # Only used for communicating with coqbot on minimization resumption
export CI_TARGET="$(cat "$DIR/coqbot.ci-target")"
export CI_BASE_BUILD_DIR="$DIR/builds/coq"
export COQ_CI_BASE_BUILD_DIR="/builds/coq/coq"
export GITHUB_MAX_CHAR_COUNT="65536"

if [[ "${CI_TARGET}" == "TAKE FROM"* ]]; then
    CI_TARGET_FILE="$(echo "${CI_TARGET}" | sed 's/^\s*TAKE FROM //g')"
    export CI_TARGET="$(cd "$DIR" && grep '^Makefile.ci:.*recipe for target.*failed' "${CI_TARGET_FILE}" | tail -1 | sed "s/^Makefile.ci:.*recipe for target '//g; s/' failed\$//g")"
fi

if [ ! -z "${FAILING_ARTIFACT_URLS}" ] && [ ! -z "${PASSING_ARTIFACT_URLS}" ] && [ ! -z "${COQ_FAILING_SHA}" ] && [ ! -z "${COQ_PASSING_SHA}" ]; then
    export RUN_KIND=coqbot-ci
else
    export RUN_KIND=coqbot
fi

function wrap_file() {
    local file="$1"
    # coqdep output needs to be pristine for use in coq_makefile;
    # coq_makefile errors if -o is given a non-relative path / a path
    # to something not in the current directory; coqchk uses -o for
    # something other than file output, so we just exclude these three
    # files
    if [[ "$file" != *.orig ]] && [[ "$file" != *coqdep* ]] && [[ "$file" != *coq_makefile* ]] && [[ "$file" != *coqchk* ]]; then
        if [ ! -f "$file.orig" ]; then
            mv "$file" "$file.orig" || exit $?
            cat > "$file" <<EOF
#!/usr/bin/env bash

args=("$PWD/$file.orig")

next_is_dir=no
next_is_special=no
next_next_is_special=no
for i in "\$@"; do
  if [ "\${next_is_dir}" == "yes" ]; then
    args+=("\$(readlink -f "\$i")")
    next_is_dir=no
    next_is_special="\${next_next_is_special}"
    next_next_is_special=no
  elif [ "\${next_is_special}" == "yes" ]; then
    args+=("\$i")
    next_is_special="\${next_next_is_special}"
    next_next_is_special=no
  elif [[ "\$i" == *".v" ]]; then
    args+=("\$(readlink -f "\$i")")
  else
    args+=("\$i")
    case "\$i" in
      -R|-Q)
        next_is_dir=yes
        next_is_special=no
        next_next_is_special=yes
        ;;
      -I|-include|-top|-topfile|-coqlib|-exlcude-dir|-load-ml-object|-load-ml-source|-load-vernac-source|-l|-load-vernac-source-verbose|-lv|-init-file|-dump-glob|-o)
        next_is_dir=yes
        next_is_special=no
        next_next_is_special=no
        ;;
      -arg|-compat|-w|-color|-diffs|-mangle-names|-set|-unset|-bytecode-compiler|-native-compiler)
        next_is_special=yes
        ;;
      -schedule-vio2vo|-schedule-vio-checking)
        next_is_special=yes
        next_next_is_special=yes
        ;;
      *)
        ;;
    esac
  fi
done

echo "MINIMIZER_DEBUG: env" >&2
env >&2
echo "MINIMIZER_DEBUG: \$0: COQPATH=\${COQPATH}" >&2
echo -n "MINIMIZER_DEBUG: exec: " >&2
printf "%q " "\${args[@]}" >&2
echo >&2
exec "\${args[@]}"
EOF
            chmod +x "$file"
        fi
    fi
}

export -f wrap_file

# print_file max_len title start_code filepath end_code
function print_file() {
    head_tail="$1"
    max_file_size="$2"
    title="$3"
    extra_title_unless_truncated="$4"
    start_code="$5"
    fname="$6"
    end_code="$7"
    filesize="$(stat -c%s "${fname}")"
    if (( filesize > max_file_size )); then
        filesize_pretty="$(numfmt --to=iec-i --suffix=B "${filesize}")"
        max_file_size_pretty="$(numfmt --to=iec-i --suffix=B "${max_file_size}")"
        case "${head_tail}" in
            head)
                contents="$(head -c ${max_file_size} "${fname}")"
                truncated=""
                ;;
            tail)
                contents="$(tail -c ${max_file_size} "${fname}")"
                truncated="last "
                ;;
            *)
                contents="Invalid head_tail='${head_tail}'$(echo; head -c ${max_file_size} "${fname}")"
                truncated=""
                ;;
        esac
        title="${title} (truncated to ${truncated}${max_file_size_pretty}; full ${filesize_pretty} file on <a href=\"${GITHUB_WORKFLOW_URL}\">GitHub Actions Artifacts</a> under <code>$(realpath --relative-to "$DIR" "${fname}")</code>)"
    else
        title="${title}${extra_title_unless_truncated}"
        contents="$(cat "${fname}")"
    fi
    echo -n "${nl}${nl}<details><summary>${title}</summary>${nl}${nl}"
    echo -n "${start_code}"
    echo -n "${contents}"
    echo -n "${end_code}"
    echo -n "${nl}</details>"
}

export -f print_file
