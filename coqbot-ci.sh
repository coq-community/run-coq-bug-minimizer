#!/usr/bin/env bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

# modified from coq/dev/ci/docker/bionic_coq/Dockerfile; TODO: better way to get the docker file
#sudo dpkg --add-architecture i386

#sudo apt-get update && sudo apt-get install --no-install-recommends -y \
    #        m4 automake autoconf time wget rsync git gcc-multilib build-essential unzip jq \
    #        perl libgmp-dev libgmp-dev:i386 \
    #        libgtksourceview-3.0-dev \
    #        texlive-latex-extra texlive-fonts-recommended texlive-xetex latexmk \
    #        python3-pip python3-setuptools python3-pexpect python3-bs4 fonts-freefont-otf \
    #        texlive-science tipa

opam switch "$COMPILER" || opam switch create "$COMPILER" || exit $?
eval $(opam env)
opam update
opam install -y ${OPAM_PACKAGES}

#COMPILER_EDGE="4.10.0"
#BASE_OPAM_EDGE="dune.2.5.1 dune-release.1.3.3 ocamlformat.0.14.2"

#opam switch create "${COMPILER_EDGE}+flambda" && eval $(opam env) && \
    #    opam install -y $BASE_OPAM $BASE_OPAM_EDGE $CI_OPAM

sudo mkdir -p /builds/coq
sudo chmod a+w /builds/coq
pushd /builds/coq
git clone https://github.com/coq/coq.git || true
(cd coq; git remote update)
cp -a coq coq-failing
cp -a coq coq-passing

pushd coq-failing
git checkout ${COQ_FAILING_SHA}
for i in ${FAILING_ARTIFACT_URLS}; do
    wget $i -O artifact.zip
    unzip -o artifact.zip
done
popd

pushd coq-passing
git checkout ${COQ_PASSING_SHA}
for i in ${PASSING_ARTIFACT_URLS}; do
    wget $i -O artifact.zip
    unzip -o artifact.zip
done
popd

for dir in /builds/coq/coq-{failing,passing}/_install_ci/bin; do
    pushd "$dir" >/dev/null
    for i in $(ls); do
        wrap_file "$i"
    done
    popd >/dev/null
done

set +x
pushd /builds/coq/coq-passing
make -f Makefile.ci GITLAB_CI=1 ${CI_TARGET} || exit $?
popd

pushd /builds/coq/coq-failing
make -f Makefile.ci GITLAB_CI=1 ${CI_TARGET} 2>&1 || true
# run it again to get the arguments to coqc
make -f Makefile.ci GITLAB_CI=1 ${CI_TARGET} 2>&1 || true
popd
