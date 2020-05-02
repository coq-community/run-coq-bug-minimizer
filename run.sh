#!/usr/bin/env bash

RC=1

function cleanup() {
    cp -f _build/default/theories/bug.v ../bug.v
    exit $RC
}

trap cleanup SIGINT SIGKILL EXIT

set -ex

opam install -y coq-equations dune
eval $(opam env)
git clone https://github.com/Mbodin/coq-prelude.git --branch=bug
cd coq-prelude
dune build @all || true
(yes "y" || true) | find-bug.py _build/default/theories/Control/List.v _build/default/theories/bug.v _build/default/theories/tmp.v -f _CoqProject -Q theories Fake -l - ../bug.log
cp -f _build/default/theories/bug.v _build/default/theories/bug0.v
(yes "y" || true) | find-bug.py _build/default/theories/bug{0,}.v _build/default/theories/tmp.v -f _CoqProject -Q theories Fake -l - ../bug2.log && RC=0
cleanup
