#!/usr/bin/env bash

set -ex

opam install -y coq-equations dune
eval $(opam env)
git clone https://github.com/Mbodin/coq-prelude.git --branch=bug
cd coq-prelude
dune build @all || true
yes "y" | find-bug.py theories/Control/List.v bug.v -f _CoqProject -l - bug.log
