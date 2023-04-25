opam install -y coq-equations
git clone https://github.com/JasonGross/metacoq.git --branch=zzz-bug-slow-qed
cd metacoq
./configure.sh local
make -C quotation/ Makefile.quotation
make safechecker template-pcuic TIMED=1 -j2
make -C quotation/ -f $(pwd)/quotation/Makefile.quotation theories/ToPCUIC/Init/Typing.vo TIMED=1 -j2
