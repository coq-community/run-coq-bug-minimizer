git clone https://github.com/skyskimmer/CertiGraph.git --branch=refine-bug
cd CertiGraph
opam update -y
opam install -y coq-vst.2.12
make -j CertiGC/refine_bug.vo
