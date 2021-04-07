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
export TMP_FILE="${BUG_TMP_DIR}/tmp.v" # must not change, since the deploy/artifact script looks for it
export FINAL_BUG_FILE="$DIR/bug.v" # must not change, since the deploy/artifact script looks for it
export BUILD_LOG="$DIR/build.log" # must not change, since the deploy/artifact script looks for it
export BUG_LOG="$DIR/bug.log" # must not change, since the deploy/artifact script looks for it

export COQBOT_URL="$(cat "$DIR/coqbot.url")"
export COMPILER="$(cat "$DIR/coqbot.compiler")"
export FAILING_ARTIFACT_URLS="$(echo $(cat "$DIR/coqbot.failing-artifact-urls"))"
export PASSING_ARTIFACT_URLS="$(echo $(cat "$DIR/coqbot.passing-artifact-urls"))"
export COQ_FAILING_SHA="$(echo $(cat "$DIR/coqbot.failing-sha"))"
export COQ_PASSING_SHA="$(echo $(cat "$DIR/coqbot.passing-sha"))"
export CI_TARGET="$(cat "$DIR/coqbot.ci-target")"
export CI_BASE_BUILD_DIR="$DIR/builds/coq"
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
    # to something not in the current directory, so we just exclude
    # these two files
    if [[ "$file" != *.orig ]] && [[ "$file" != *coqdep* ]] && [[ "$file" != *coq_makefile* ]]; then
        if [ ! -f "$file.orig" ]; then
            mv "$file" "$file.orig"
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

echo "MINIMIZER_DEBUG: \$0: COQPATH=\$COQPATH" >&2
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

if [ -z "${MAX_FILE_SIZE}" ]; then
    # 1MiB in bytes
    MAX_FILE_SIZE="$((1 * 1024 * 1024))"
fi

# print_file title start_code filepath end_code
function print_file() {
    filesize="$(stat -c%s "$3")"
    title="$1"
    if (( filesize > MAX_FILE_SIZE )); then
        title="${title} (truncated to $(numfmt --to=iec-i --suffix=B "${MAX_FILE_SIZE}"); full file on [GitHub Actions Artifacts](${GITHUB_WORKFLOW_URL}) under ${backtick}$(realpath --relative-to "$DIR" "$3")${backtick})"
        contents="$(head -c ${MAX_FILE_SIZE} "$3")"
    else
        contents="$(cat "$3")"
    fi
    echo -n "${nl}${nl}<details><summary>${title}</summary>${nl}${nl}"
    echo -n "$2" # start code
    echo -n "${contents}"
    echo -n "$4" # end code
    echo -n "${nl}</details>"
}

export -f print_file
