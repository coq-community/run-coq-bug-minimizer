opam install -y coq-equations
git clone https://github.com/JasonGross/metacoq.git --branch=zzz-bug-slow-qed
cd metacoq
./configure.sh local
make quotation TIMED=1 -j2
