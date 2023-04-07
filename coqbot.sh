#!/usr/bin/env bash
opam install -y coq-equations
git clone https://github.com/JasonGross/metacoq.git --branch=zzz-bug-equations-anomaly
cd metacoq
./configure.sh local
make safechecker TIMED=1 -j2
