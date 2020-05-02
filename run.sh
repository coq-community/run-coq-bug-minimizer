#!/usr/bin/env bash

function cleanup() {
    cp -f theories/bug.v ../bug.v
    exit 1
}

trap cleanup SIGINT SIGKILL EXIT

set -ex

opam install -y coq-equations dune
eval $(opam env)
git clone https://github.com/Mbodin/coq-prelude.git --branch=bug
cd coq-prelude
dune build @all || true
yes "y" | find-bug.py theories/Control/List.v theories/bug.v -f _CoqProject -l - ../bug.log
