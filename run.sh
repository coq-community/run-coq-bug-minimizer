#!/usr/bin/env bash

RC=1

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

function cleanup() {
    cp -f "bug_01.v" "$DIR/bug.v"
    exit $RC
}

trap cleanup SIGINT SIGKILL EXIT

set -ex

opam install -y coq-ext-lib # dune
eval $(opam env)
#git clone https://github.com/satnam6502/oak-hardware
#cd oak-hardware
#git checkout 38971a7d0f8aa04b6fa4e21d1dfda3990ecf2c66
#cd cava/cava
mkdir temp
cd temp
wget https://github.com/coq/coq/files/4698509/bug.v.zip
unzip bug.v.zip

#make coq || true
(yes "y" || true) | find-bug.py bug.v bug_01.v tmp.v --inline-user-contrib -l - "$DIR/bug.log" && RC=0
#(yes "y" || true) | find-bug.py _build/default/theories/bug{0,}.v _build/default/theories/tmp.v -f _CoqProject -Q theories Fake -l - ../bug2.log && RC=0
cleanup
