#!/usr/bin/env bash

set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

sudo apt-get update -y
sudo apt-get install -y curl

opam switch "$COMPILER"
eval $(opam env)

mkdir -p "${CI_BASE_BUILD_DIR}"
pushd "${CI_BASE_BUILD_DIR}"
git clone https://github.com/coq/coq.git || true
printf '\n\tfetch = +refs/pull/*/head:refs/remotes/origin/pr/*\n' >> coq/.git/config
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

for dir in "${CI_BASE_BUILD_DIR}"/coq-{failing,passing}/_install_ci/bin; do
    pushd "$dir" >/dev/null
    for i in $(ls); do
        wrap_file "$i"
    done
    popd >/dev/null
done

set +x

pushd "${CI_BASE_BUILD_DIR}"/coq-passing
make -f Makefile.ci GITLAB_CI=1 ${CI_TARGET}
popd

pushd "${CI_BASE_BUILD_DIR}"/coq-failing
make -f Makefile.ci GITLAB_CI=1 ${CI_TARGET} 2>&1 || true
popd

set -x
