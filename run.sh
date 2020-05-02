#!/usr/bin/env bash

function cleanup() {
    cp -f _build/default/theories/bug.v ../bug.v
    exit 1
}

trap cleanup SIGINT SIGKILL EXIT

set -ex

opam install -y coq-equations dune
eval $(opam env)
git clone https://github.com/Mbodin/coq-prelude.git --branch=bug
cd coq-prelude
dune build @all || true
(yes "y" || true) | find-bug.py _build/default/theories/Control/List.v _build/default/theories/bug.v _build/default/theories/tmp.v -f _CoqProject -Q theories Fake -l - ../bug.log
