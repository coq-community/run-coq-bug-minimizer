# modified from coq/dev/ci/docker/bionic_coq/Dockerfile; TODO: better way to get the docker file
DEBIAN_FRONTEND="noninteractive"

sudo dpkg --add-architecture i386

#sudo apt-get update && sudo apt-get install --no-install-recommends -y \
#        m4 automake autoconf time wget rsync git gcc-multilib build-essential unzip jq \
#        perl libgmp-dev libgmp-dev:i386 \
#        libgtksourceview-3.0-dev \
#        texlive-latex-extra texlive-fonts-recommended texlive-xetex latexmk \
#        python3-pip python3-setuptools python3-pexpect python3-bs4 fonts-freefont-otf \
#        texlive-science tipa

COMPILER="4.05.0"

BASE_OPAM="num zarith.1.9.1 ocamlfind.1.8.1 ounit2.2.2.3 odoc.1.5.0"
CI_OPAM="menhir.20190626 ocamlgraph.1.8.8"
BASE_ONLY_OPAM="elpi.1.11.0"

opam switch "$COMPILER" || opam switch create "$COMPILER" || exit $?
eval $(opam env)
opam update
opam install -y $BASE_OPAM $CI_OPAM $BASE_ONLY_OPAM

COMPILER_EDGE="4.10.0"
BASE_OPAM_EDGE="dune.2.5.1 dune-release.1.3.3 ocamlformat.0.14.2"

#opam switch create "${COMPILER_EDGE}+flambda" && eval $(opam env) && \
#    opam install -y $BASE_OPAM $BASE_OPAM_EDGE $CI_OPAM

if [ ! -f coq_failing.zip ]; then
    # edge+flambda
    #wget https://gitlab.com/coq/coq/-/jobs/735893270/artifacts/download -O coq_failing.zip
    # build:base
    wget https://gitlab.com/coq/coq/-/jobs/735893267/artifacts/download -O coq_failing.zip
fi
if [ ! -f coq_passing.zip ]; then
    # edge+flambda
    # wget https://gitlab.com/coq/coq/-/jobs/735636738/artifacts/download -O coq_passing.zip
    # build:base
    wget https://gitlab.com/coq/coq/-/jobs/735636736/artifacts/download -O coq_passing.zip
fi
COQ_FAILING_SHA=708c67a75ee72ac2b8e6330bef10a9665c3366fd
COQ_PASSING_SHA=9278a6ec5b0cc33691b441beaa73cf38f04f4cbb
sudo mkdir -p /builds/coq
sudo chmod a+w /builds/coq
pushd /builds/coq
# rm -rf coq
#rm -rf coq-failing coq-passing
git clone https://github.com/coq/coq.git || true
(cd coq; git remote update)
cp -a coq coq-failing
cp -a coq coq-passing
(cd coq-failing; git checkout ${COQ_FAILING_SHA})
(cd coq-passing; git checkout ${COQ_PASSING_SHA})
popd
unzip -n coq_failing.zip -d /builds/coq/coq-failing
unzip -n coq_passing.zip -d /builds/coq/coq-passing

for dir in /builds/coq/coq-{failing,passing}/_install_ci/bin; do
    pushd "$dir" >/dev/null
    for i in $(ls); do
        if [[ "$i" != *.orig ]]; then
            if [ ! -f "$i.orig" ]; then
                mv "$i" "$i.orig"
                cat > "$i" <<EOF
#!/usr/bin/env bash
echo "MINIMIZER_DEBUG: \$0: COQPATH=\$COQPATH" >&2
function call_orig() {
#  set -ex
  exec $dir/$i.orig "\$@"
}

function quote() {
  xargs printf "%q " >&2
}

echo -n "MINIMIZER_DEBUG: exec: " >&2
echo "$dir/$i.orig" | quote
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
exec "$dir/$i.orig" "\$@"
EOF
                chmod +x "$i"
            fi
        fi
    done
    popd >/dev/null
done

function try_find_file() {
    file="$1"
    file="$(echo "$file" | sed 's,^\./,,g')"
    newfile="$file"
    findfile="$(find . -wholename "*${file}" | head -1)"
    if [ -f "$file" ]; then
        newfile="$(readlink -f "$file")"
    elif [ ! -z "$findfile" ]; then
        newfile="$(readlink -f "$findfile")"
    fi
    if [ "$newfile" != "$file" ]; then
        echo "$newfile"
    else
        echo "$1"
    fi
}

function absolutize_files() {
    while read line; do
        enter="$(echo "$line" | grep "make[^:]*: Entering directory '" | grep -o "'[^']*'" | sed "s/'//g")"
        leave="$(echo "$line" | grep "make[^:]*: Leaving directory '" | grep -o "'[^']*'" | sed "s/'//g")"
        file="$(echo "$line" | grep -o 'File "[^"]*", line [0-9-]*, characters [0-9-]*:' | grep -o '"[^"]*"' | sed 's/"//g')"
        coqcfile="$(echo "$line" | grep '"[^"]*coqc".* [^ ]*\.v$' | grep -o ' [^ ]*\.v$' | sed 's/^ //g')"
        if [ ! -z "$enter" ]; then
            echo "$line"
            pushd "$enter" >/dev/null
        elif [ ! -z "$leave" ]; then
            echo "$line"
            popd >/dev/null
        elif [ ! -z "$file" ]; then
            newfile="$(try_find_file "$file")"
            if [ "$newfile" != "$file" ]; then
                echo "$line" | sed 's|File "[^"]*", line |File "'"$newfile"'", line |g'
            else
                echo "$line"
            fi
        elif [ ! -z "$coqcfile" ]; then
            newfile="$(try_find_file "$coqcfile")"
            if [ "$newfile" != "$coqcfile" ]; then
                echo "$line" | sed 's| [^ ]*\.v$| '"$newfile"'|g'
            else
                echo "$line"
            fi
        else
            echo "$line"
        fi
    done
}

#TARGET="$(grep '^make: ... .ci-.* Error' failing-log.log | tail -1 | grep -o '\[[^]]*\]' | sed 's/\[//g; s/\]//g')"
TARGET="$(grep '^Makefile.ci:.*recipe for target.*failed' failing-log.log | tail -1 | sed "s/^Makefile.ci:.*recipe for target '//g; s/' failed\$//g")"
set +x
pushd /builds/coq/coq-passing
{ make -f Makefile.ci GITLAB_CI=1 ${TARGET} 2>&1 | absolutize_files; } || exit $?
popd
pushd /builds/coq/coq-failing
{ make -f Makefile.ci GITLAB_CI=1 ${TARGET} 2>&1 | absolutize_files; } || true
# run it again to get the arguments to coqc
{ make -f Makefile.ci GITLAB_CI=1 ${TARGET} 2>&1 | absolutize_files; } || true
popd
