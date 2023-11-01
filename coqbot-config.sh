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
export VERBOSE_BUG_LOG="$DIR/bug.verbose.log" # must not change, since the deploy/artifact script looks for it
export BACKUP_BUG_LOG="$DIR/bug.backup.log"
export METADATA_FILE="$DIR/metadata" # must not change, since the deploy/artifact script looks for it
export FINAL_TMP_FOLDER="$DIR/tmp" # must not change, since the deploy/artifact script looks for it

export TIMEDOUT_STAMP_FILE="$DIR/timedout"

export COQBOT_URL="$(cat "$DIR/coqbot.url")"
export COQBOT_RESUME_MINIMIZATION_URL="$(cat "$DIR/coqbot.resume-minimization-url" 2>/dev/null)"
export SURVEY_URL="$(cat "$DIR/coqbot.survey-url")"
export SURVEY_PR_URL_PARAMETER="$(cat "$DIR/coqbot.survey-pr-url-parameter")"
export ISSUE_NUMBER="$(cat "$DIR/coqbot.issue-number")"
export COMPILER="$(cat "$DIR/coqbot.compiler")"
export FAILING_ARTIFACT_URLS="$(echo $(cat "$DIR/coqbot.failing-artifact-urls"))"
export PASSING_ARTIFACT_URLS="$(echo $(cat "$DIR/coqbot.passing-artifact-urls"))"
export COQ_FAILING_SHA="$(echo $(cat "$DIR/coqbot.failing-sha"))"
export COQ_PASSING_SHA="$(echo $(cat "$DIR/coqbot.passing-sha"))"
# this one is tricky, we want to include trailing newlines so we don't
# lose potentially-empty extra arguments at the end, so we do as in
# https://stackoverflow.com/a/40717560/377022
RESUMPTION_ARGS="$(cat "$DIR/coqbot.resumption-args" 2>/dev/null; printf '.\n')"
RESUMPTION_ARGS="${RESUMPTION_ARGS:0:-1}"
export RESUMPTION_ARGS # Only used for communicating with coqbot on minimization resumption
export CI_TARGET="$(cat "$DIR/coqbot.ci-target")"
export CI_BASE_BUILD_DIR="$DIR/builds/coq"
export COQ_CI_BASE_BUILD_DIR="/builds/coq/coq"
export GITHUB_MAX_CHAR_COUNT="65536"
IFS=$'\n' export EXTRA_MINIMIZER_ARGUMENTS=($(cat "$DIR/coqbot.extra-args"))

if [[ "${CI_TARGET}" == "TAKE FROM"* ]]; then
    CI_TARGET_FILE="$(printf "%s\n" "${CI_TARGET}" | sed 's/^\s*TAKE FROM //g')"
    if [ -f "${CI_TARGET_FILE}" ]; then
        export CI_TARGET="$(cd "$DIR" && grep '^Makefile.ci:.*recipe for target.*failed' "${CI_TARGET_FILE}" | tail -1 | sed "s/^Makefile.ci:.*recipe for target '//g; s/' failed\$//g")"
    else
        export CI_TARGET=""
    fi
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

DIR="\$( cd "\$( dirname "\${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

args=("\$DIR/$file.orig")

next_is_dir=no
next_is_special=no
next_next_is_special=no
fname=""
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
    fname="\$fname \$i"
    args+=("\$i") # ("\$(readlink -f "\$i")") # we absolutize this later instead of now, to preserve output tests in HB
  else
    args+=("\$i")
    case "\$i" in
      -R|-Q)
        next_is_dir=yes
        next_is_special=no
        next_next_is_special=yes
        ;;
      -I|-include|-coqlib|-exlcude-dir|-load-ml-object|-load-ml-source|-load-vernac-source|-l|-load-vernac-source-verbose|-lv|-init-file|-dump-glob|-o|-time-file)
        next_is_dir=yes
        next_is_special=no
        next_next_is_special=no
        ;;
      -arg|-compat|-w|-color|-diffs|-mangle-names|-set|-unset|-top|-topfile|-bytecode-compiler|-native-compiler)
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

debug_prefix="\$(mktemp --tmpdir tmp-coqbot-minimizer.XXXXXXXXXX)"
printf "%s" "\$0" > "\${debug_prefix}"
printf "%s" "\$COQPATH" > "\${debug_prefix}.coqpath"
printf "%s" "\$(pwd)" > "\${debug_prefix}.pwd"
printf "%q " "\${args[@]}" > "\${debug_prefix}.exec"

# extra, not strictly needed
>&2 printf "MINIMIZER_DEBUG_EXTRA: coqc: %s\n" "\$0"
>&2 printf "MINIMIZER_DEBUG_EXTRA: coqpath: %s\n" "\$(cat "\${debug_prefix}.coqpath")"
>&2 printf "MINIMIZER_DEBUG_EXTRA: pwd: PWD=%s\n" "\$(cat "\${debug_prefix}.pwd")"
>&2 printf "MINIMIZER_DEBUG_EXTRA: exec: %s\n" "\$(cat "\${debug_prefix}.exec")"
# the two important lines
>&2 printf "MINIMIZER_DEBUG: info: %s\n" "\${debug_prefix}"
>&2 printf "MINIMIZER_DEBUG: files: %s\n" "\${fname}"

exec "\${args[@]}"
EOF
            chmod +x "$file"
        fi
    fi
}

export -f wrap_file

function wrap_opam() {
    local file="$(which opam)"
    if [ ! -f "$file.orig" ]; then
        sudo mv "$file" "$file.orig" || exit $?
        sudo touch "$file"
        sudo chmod a+rw "$file"
        cat > "$file" <<EOF
#!/usr/bin/env bash

DIR="\$( cd "\$( dirname "\${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

source "$DIR/coqbot-config.sh"

"$file.orig" "\$@" || exit \$?

eval "\$("$file.orig" env)"

printf '::group::opam wrap files\n' >&2
printf 'wrapping %s\n' "\$(which opam)" >&2
wrap_opam $@
for i in $@; do
    printf "attempting to wrap %s\n" "\$i" >&2
    if command -v "\$i" >/dev/null; then
        printf "wrapping %s" "\$(which "\$i")" >&2
        pushd "\$(dirname "\$(which "\$i")")" >/dev/null
        wrap_file "\$i"
        popd >/dev/null
    fi
done
printf '::endgroup::\n' >&2
EOF
        sudo chmod --reference="$file.orig" "$file"
    fi
}

export -f wrap_opam

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
    head_tail_separator="$(printf '\n\n[...]\n\n')"
    if (( filesize > max_file_size )); then
        case "${head_tail}" in
            head-tail)
                max_filesize="$(( ( ${max_file_size} - ${#head_tail_separator} ) / 2 ))"
                contents="$(head -c ${max_file_size} "${fname}")${head_tail_separator}$(tail -c ${max_file_size} "${fname}")"
                truncated="first and last "
                ;;
            head)
                contents="$(head -c ${max_file_size} "${fname}")"
                truncated=""
                ;;
            tail)
                contents="$(tail -c ${max_file_size} "${fname}")"
                truncated="last "
                ;;
            *)
                contents="Invalid head_tail='${head_tail}'$(printf '\n'; head -c ${max_file_size} "${fname}")"
                truncated=""
                ;;
        esac
        filesize_pretty="$(numfmt --to=iec-i --suffix=B "${filesize}")"
        max_file_size_pretty="$(numfmt --to=iec-i --suffix=B "${max_file_size}")"
        title="${title} (truncated to ${truncated}${max_file_size_pretty}; full ${filesize_pretty} file on <a href=\"${GITHUB_WORKFLOW_URL}\">GitHub Actions Artifacts</a> under <code>$(realpath --relative-to "$DIR" "${fname}")</code>)"
    else
        title="${title}${extra_title_unless_truncated}"
        contents="$(cat "${fname}")"
    fi
    printf "\n\n<details><summary>%s</summary>\n\n" "${title}"
    printf "%s" "${start_code}"
    printf "%s" "${contents}"
    printf "%s" "${end_code}"
    printf "\n</details>"
}

export -f print_file
