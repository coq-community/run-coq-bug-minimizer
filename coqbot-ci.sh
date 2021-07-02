#!/usr/bin/env bash

set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

echo '::group::install dependencies'
sudo apt-get update -y
sudo apt-get install -y curl
echo '::endgroup::'

echo "::group::opam switch '$COMPILER'"
echo "::warning::Using opam switch '$COMPILER'"
opam switch "$COMPILER"
eval $(opam env)
echo '::endgroup::'

mkdir -p "${CI_BASE_BUILD_DIR}"
pushd "${CI_BASE_BUILD_DIR}"
echo '::group::clone coq'
git clone https://github.com/coq/coq.git || true
sed 's,^\(\s*\)\(fetch =.*\)$,\1\2\n\1fetch = +refs/pull/*/head:refs/remotes/origin/pr/*,g' -i coq/.git/config
cat coq/.git/config
(cd coq; git remote update >/dev/null)
cp -a coq coq-failing
cp -a coq coq-passing
echo '::endgroup::'

echo "::group::download failing artifacts @ ${COQ_FAILING_SHA} ${FAILING_ARTIFACT_URLS}"
echo "::warning::download failing artifacts @ ${COQ_FAILING_SHA} ${FAILING_ARTIFACT_URLS}"
pushd coq-failing
git checkout ${COQ_FAILING_SHA}
for i in ${FAILING_ARTIFACT_URLS}; do
    hash="$(echo "$i" | sha1sum | cut -d" " -f1)"
    wget $i -O "artifact-$hash.zip"
    unzip -o "artifact-$hash.zip"
done
popd
echo '::endgroup::'

echo "::group::download passing artifacts @ ${COQ_PASSING_SHA} ${PASSING_ARTIFACT_URLS}"
echo "::warning::download passing artifacts @ ${COQ_PASSING_SHA} ${PASSING_ARTIFACT_URLS}"
pushd coq-passing
git checkout ${COQ_PASSING_SHA}
for i in ${PASSING_ARTIFACT_URLS}; do
    hash="$(echo "$i" | sha1sum | cut -d" " -f1)"
    wget $i -O "artifact-$hash.zip"
    unzip -o "artifact-$hash.zip"
done
popd
echo '::endgroup::'

echo '::group::wrap binaries'
for dir in "${CI_BASE_BUILD_DIR}"/coq-{failing,passing}/_install_ci/bin; do
    pushd "$dir" >/dev/null
    for i in $(ls); do
        wrap_file "$i"
    done
    popd >/dev/null
done
echo '::endgroup::'

set +x

sudo mkdir -p "${COQ_CI_BASE_BUILD_DIR}"
sudo rm -rf "${COQ_CI_BASE_BUILD_DIR}"

echo "::group::make ${CI_TARGET} (passing)"
mv "${CI_BASE_BUILD_DIR}"/coq-passing "${COQ_CI_BASE_BUILD_DIR}"
pushd "${COQ_CI_BASE_BUILD_DIR}"
make -f Makefile.ci GITLAB_CI=1 ${CI_TARGET}
popd
mv "${COQ_CI_BASE_BUILD_DIR}" "${CI_BASE_BUILD_DIR}"/coq-passing
echo '::endgroup::'

echo "::group::make ${CI_TARGET} (failing)"
mv "${CI_BASE_BUILD_DIR}"/coq-failing "${COQ_CI_BASE_BUILD_DIR}"
pushd "${COQ_CI_BASE_BUILD_DIR}"
{ make -f Makefile.ci GITLAB_CI=1 ${CI_TARGET} 2>&1 | sed "s|${COQ_CI_BASE_BUILD_DIR}/|${CI_BASE_BUILD_DIR}/coq-failing/|g"; } || true
popd
mv "${COQ_CI_BASE_BUILD_DIR}" "${CI_BASE_BUILD_DIR}"/coq-failing
echo '::endgroup::'

set -x
