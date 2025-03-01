#!/usr/bin/env bash

set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

printf "::group::opam switch '%s'\n" "$COMPILER"
printf "::warning::Using opam switch '%s'\n" "$COMPILER"
opam switch "$COMPILER"
eval $(opam env)
printf "::warning::which ocamlfind: '%s'\n" "$(which ocamlfind)"
printf "::warning::ocamlfind ocamlopt -v: %s\n" "$(ocamlfind ocamlopt -v | tr '\n' '\r' | sed 's/\r/%0A/g')"
printf '::endgroup::\n'

printf '::group::df -h\n'
df -h
printf '::endgroup::\n'

mkdir -p "${CI_BASE_BUILD_DIR}"
pushd "${CI_BASE_BUILD_DIR}"
printf '::group::clone coq\n'
git clone https://github.com/coq/coq.git || true
sed 's,^\(\s*\)\(fetch =.*\)$,\1\2\n\1fetch = +refs/pull/*/head:refs/remotes/origin/pr/*,g' -i coq/.git/config
cat coq/.git/config
(cd coq; git remote update >/dev/null)
cp -a coq coq-failing
cp -a coq coq-passing
printf '::endgroup::\n'

printf '::group::df -h\n'
df -h
printf '::endgroup::\n'

printf "::group::download failing artifacts @ %s %s\n" "${COQ_FAILING_SHA}" "${FAILING_ARTIFACT_URLS}"
printf "::warning::download failing artifacts @ %s %s\n" "${COQ_FAILING_SHA}" "${FAILING_ARTIFACT_URLS}"
pushd coq-failing
# set up saved_build_ci -> _build_ci symlink so that unzips from https://github.com/coq/coq/pull/19925 go to the right place
mkdir -p _build_ci
ln -s _build_ci saved_build_ci
git checkout ${COQ_FAILING_SHA}
for i in ${FAILING_ARTIFACT_URLS}; do
    hash="$(printf "%s" "$i" | sha1sum | cut -d" " -f1)"
    wget $i -O "artifact-$hash.zip"
    unzip -o "artifact-$hash.zip"
done
popd
printf '::endgroup::\n'

printf '::group::df -h\n'
df -h
printf '::endgroup::\n'

printf "::group::download passing artifacts @ %s %s\n" "${COQ_PASSING_SHA}" "${PASSING_ARTIFACT_URLS}"
printf "::warning::download passing artifacts @ %s %s\n" "${COQ_PASSING_SHA}" "${PASSING_ARTIFACT_URLS}"
pushd coq-passing
# set up saved_build_ci -> _build_ci symlink so that unzips from https://github.com/coq/coq/pull/19925 go to the right place
mkdir -p _build_ci
ln -s _build_ci saved_build_ci
git checkout ${COQ_PASSING_SHA}
for i in ${PASSING_ARTIFACT_URLS}; do
    hash="$(printf "%s" "$i" | sha1sum | cut -d" " -f1)"
    wget $i -O "artifact-$hash.zip"
    unzip -o "artifact-$hash.zip"
done
popd
printf '::endgroup::\n'

printf '::group::df -h\n'
df -h
printf '::endgroup::\n'

printf '::group::set up COQ_CI_BASE_BUILD_DIR: %s\n' "${COQ_CI_BASE_BUILD_DIR}"
sudo mkdir -p "${COQ_CI_BASE_BUILD_DIR}"
sudo rm -rf "${COQ_CI_BASE_BUILD_DIR}"
printf '::endgroup::\n'

printf '::group::wrap binaries\n'
for coqdir in "${CI_BASE_BUILD_DIR}"/coq-{failing,passing}; do
    tmpcoqdir="${COQ_CI_BASE_BUILD_DIR}"
    # mv "${coqdir}" "${tmpcoqdir}"
    ln -s "${coqdir}" "${tmpcoqdir}"
    pushd "${tmpcoqdir}/_install_ci/bin" >/dev/null
    printf "::warning::(%s) %s/coqc --config: %s\n" "${coqdir}" "$(pwd)" "$(./coqc --config | tr '\n' '\r' | sed 's/\r/%0A/g')"
    ./coqc --config | sed "s,${tmpcoqdir}/,${coqdir}/,g; "'s,^\([^=]*\)=\(.*\)$,\1="\2",g' > coq_environment.txt
    printf "::warning::(%s) setting up coq_environment.txt: %s\n" "${coqdir}" "$(cat coq_environment.txt | tr '\n' '\r' | sed 's/\r/%0A/g')"
    for i in $(ls); do
        wrap_file "$i"
    done
    popd >/dev/null
    # mv "${tmpcoqdir}" "${coqdir}"
    rm "${tmpcoqdir}"
done
printf '::endgroup::\n'

set +x

printf "::group::make %s (passing)\n" "${CI_TARGET}"
# mv "${CI_BASE_BUILD_DIR}"/coq-passing "${COQ_CI_BASE_BUILD_DIR}"
ln -s "${CI_BASE_BUILD_DIR}"/coq-passing "${COQ_CI_BASE_BUILD_DIR}"
pushd "${COQ_CI_BASE_BUILD_DIR}"
make -f Makefile.ci GITLAB_CI=1 ${CI_TARGET}
popd
# mv "${COQ_CI_BASE_BUILD_DIR}" "${CI_BASE_BUILD_DIR}"/coq-passing
rm "${COQ_CI_BASE_BUILD_DIR}"
printf '::endgroup::\n'

printf "::group::make %s (failing)\n" "${CI_TARGET}"
# mv "${CI_BASE_BUILD_DIR}"/coq-failing "${COQ_CI_BASE_BUILD_DIR}"
ln -s "${CI_BASE_BUILD_DIR}"/coq-failing "${COQ_CI_BASE_BUILD_DIR}"
pushd "${COQ_CI_BASE_BUILD_DIR}"
{ make -f Makefile.ci GITLAB_CI=1 ${CI_TARGET} 2>&1 | sed "s|${COQ_CI_BASE_BUILD_DIR}/|${CI_BASE_BUILD_DIR}/coq-failing/|g"; } || true
popd
# mv "${COQ_CI_BASE_BUILD_DIR}" "${CI_BASE_BUILD_DIR}"/coq-failing
rm "${COQ_CI_BASE_BUILD_DIR}"
printf '::endgroup::\n'

set -x
