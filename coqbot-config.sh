#!/usr/bin/env bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

export nl=$'\n'
export backtick='`'
export start_code='```'"${nl}"
export start_coq_code='```coq'"${nl}"
export end_code="${nl}"'```'
export COQBOT_URL="$(cat "$DIR/coqbot.url")"
export COMPILER="$(cat "$DIR/coqbot.compiler")"
export OPAM_PACKAGES="$(cat "$DIR/coqbot.opam-packages")"
export FAILING_ARTIFACT_URLS="$(echo $(cat "$DIR/coqbot.failing-artifact-urls"))"
export PASSING_ARTIFACT_URLS="$(echo $(cat "$DIR/coqbot.passing-artifact-urls"))"
export COQ_FAILING_SHA="$(echo $(cat "$DIR/coqbot.failing-sha"))"
export COQ_PASSING_SHA="$(echo $(cat "$DIR/coqbot.passing-sha"))"
export CI_TARGET="$(cat "$DIR/coqbot.ci-target")"
if [[ "${CI_TARGET}" == "TAKE FROM"* ]]; then
    CI_TARGET_FILE="$(echo "${CI_TARGET}" | sed 's/^\s*TAKE FROM //g')"
    export CI_TARGET="$(grep '^Makefile.ci:.*recipe for target.*failed' "$(cd "$DIR" && cat "${CI_TARGET_FILE}")" | tail -1 | sed "s/^Makefile.ci:.*recipe for target '//g; s/' failed\$//g")"
fi

if [ ! -z "${FAILING_ARTIFACT_URLS}" ] && [ ! -z "${PASSING_ARTIFACT_URLS}" ] && [ ! -z "${FAILING_SHA}" ] && [ ! -z "${PASSING_SHA}" ]; then
    export RUN_KIND=coqbot-ci
else
    export RUN_KIND=coqbot
fi

function wrap_file() {
    local file="$1"
    if [[ "$file" != *.orig ]] && [[ "$file" != *coqdep* ]]; then
        if [ ! -f "$file.orig" ]; then
            mv "$file" "$file.orig"
            cat > "$file" <<EOF
#!/usr/bin/env bash
echo "MINIMIZER_DEBUG: \$0: COQPATH=\$COQPATH" >&2
function call_orig() {
#  set -ex
  exec $PWD/$file.orig "\$@"
}

function quote() {
  xargs printf "%q " >&2
}

echo -n "MINIMIZER_DEBUG: exec: " >&2
echo "$PWD/$file.orig" | quote
next_is_dir=no
next_is_special=no
next_next_is_special=no
for i in "\$@"; do
  if [ "\${next_is_dir}" == "yes" ]; then
    readlink -f "\$i" | quote
    next_is_dir=no
    next_is_special="\${next_next_is_special}"
    next_next_is_special=no
  elif [ "\${next_is_special}" == "yes" ]; then
    echo "\$i" | quote
    next_is_special="\${next_next_is_special}"
    next_next_is_special=no
  elif [[ "\$i" == *".v" ]]; then
    readlink -f "\$i" | quote
  else
    echo "\$i" | quote
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
echo >&2
exec "$PWD/$file.orig" "\$@"
EOF
            chmod +x "$file"
        fi
    fi
}

export -F wrap_file
