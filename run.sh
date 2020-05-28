#!/usr/bin/env bash

RC=1

function cleanup() {
    cp -f _build/default/theories/bug.v ../bug.v
    exit $RC
}

trap cleanup SIGINT SIGKILL EXIT

set -ex

# opam install -y coq-equations dune
eval $(opam env)
git clone https://github.com/satnam6502/oak-hardware
cd oak-hardware
git checkout 38971a7d0f8aa04b6fa4e21d1dfda3990ecf2c66
cd cava/cava

make coq || true
(yes "y" || true) | find-bug.py ./Cava/Arrow/Instances/Netlist.v Cava/bug.v Cava/tmp.v -f _CoqProject -l - ../../../bug.log
cp -f Cava/bug.v ../../../bug.v
#(yes "y" || true) | find-bug.py _build/default/theories/bug{0,}.v _build/default/theories/tmp.v -f _CoqProject -Q theories Fake -l - ../bug2.log && RC=0
cleanup
