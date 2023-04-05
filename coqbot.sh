#!/usr/bin/env bash
opam install -y coq-equations
git clone https://github.com/JasonGross/metacoq.git --branch=coq-8.16+all-polymorphic
cd metacoq
./configure.sh local
make safechecker TIMED=1 -j2
