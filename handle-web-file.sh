#!/usr/bin/env bash
# handle-web-file.sh [LINK_TEXT] URL
#
# Downloads an archive and tries to guess how to build the coq
# development from it

set -ex

descr="$1"
url="$2"

if [ -z "$url" ]; then
    url="$descr"
    descr=""
fi

if [ -z "$url" ]; then
    >&2 echo "USAGE: $0 [LINK_TEXT] URL"
    exit 1
fi

rawfname="$(basename "$url")"
extension="${rawfname##*.}"
base="${rawfname%%.*}"
fname="downloaded-$rawfname"
qfname="$(printf "%q" "$fname")"
qextension="$(printf "%q" "$extension")"
wget "$url" -O "$fname"

success="no"

function trial_extract_raw() {
    if [ "$success" == "no" ]; then
        rm -rf bug-output
        mkdir -p bug-output
        cd bug-output
        bash -c "$1" && { success="yes"; cd ..; } || { cd ..; rm -rf bug-output; }
    fi
}

function trial_extract() {
    trial_extract_raw "$(printf "%q " "$@")"
}

function succeed() {
    success="yes"
}

function run_unique_file_pattern() {
    count="$(find . -name "$1" -executable -type f | wc -l)"
    rv=1
    if [ "$count" -eq 1 ]; then
        rv=0
        f="$(find . -name "$1" -executable -type f)"
        dirf="$(dirname "$f")"
        f="$(basename "$f")"
        pushd "$dirf"
        ./"$f" || { rv=$?; }
        popd
    fi
    return $rv
}

function run_first_unique_file_patterns() {
    success="no"
    for name in "$@"; do
        test "$success" == "yes" || { run_unique_file_pattern "$name" && succeed || true; }
    done
    test "$success" == "yes"
}

function try_autogen() {
    run_first_unique_file_patterns autogen autogen.sh
}

function try_configure() {
    run_first_unique_file_patterns configure configure.sh
}

function try_make() {
    fs="$(find . \( -name GNUmakefile -o -name makefile -o -name Makefile \) -type f)"
    count="$(find . \( -name GNUmakefile -o -name makefile -o -name Makefile \) -type f | wc -l)"
    if [ "$count" -eq 1 ]; then
        dirf="$(dirname "$fs")"
        f="$(basename "$fs")"
        pushd "$dirf"
        make || true
        popd
        return 0
    fi
    return 1
}

function try_autogen_configure_make() {
    try_make || { try_configure && try_make; } || { try_autogen && try_configure && try_make; }
}

function try_coq_makefile() {
    fs="$(find . \( -name "_CoqProject" -o -name "CoqProject" \) -type f)"
    count="$(find . \( -name "_CoqProject" -o -name "CoqProject" \) -type f | wc -l)"
    if [ "$count" -eq 1 ]; then
        dirf="$(dirname "$fs")"
        f="$(basename "$fs")"
        pushd "$dirf"
        coq_makefile -f "$f" -o Makefile
        make || true
        popd
        return 0
    fi
    return 1
}

function try_coqc() {
    fs="$(find . -name "*.v" -type f)"
    count="$(find . -name "*.v" -type f | wc -l)"
    if [ "$count" -eq 1 ]; then
        dirf="$(dirname "$fs")"
        f="$(basename "$fs")"
        pushd "$dirf"
        coqc -q "$f" || true
        popd
        return 0
    elif [ "$count" -gt 1 ]; then
        find . -name "*.v" -type f | xargs coq_makefile -o Makefile
        make || true
        return 0
    else
        return 1
    fi
}

trial_extract tar -xvf "../$fname"
trial_extract unzip "../$fname"
trial_extract_raw "file ../$qfname | grep -q text && cp ../$qfname downloaded_bug.v"
trial_extract_raw "test x$qextension == xtxt && cp ../$qfname downloaded_bug.v"
for kind in --bzip2 --xz --lzip --lzma --lzop --gunzip --uncompress --zstd; do
    trial_extract tar $kind -xvf "../$fname"
done

if [ "$success" == "no" ]; then
    >&2 echo "ERROR: Could not recognize $fname as archive or .v file"
    >&2 file "$fname"
    exit 1
fi

cd bug-output
try_autogen_configure_make || try_coq_makefile || try_coqc
