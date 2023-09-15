git clone https://github.com/JasonGross/CertiGraph.git --branch=patch-1
cd CertiGraph
opam update -y
opam install -y coq-vst.2.12
make -j CertiGC/refine_bug.vo
