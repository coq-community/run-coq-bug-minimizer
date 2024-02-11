git clone git@github.com:meta-introspector/metacoq.git --branch=feature/ltac_debug
cd metacoq
git checkout 1bc110910d49e2bcf3f3eb111527d4be0d4ad0c7
opam install --deps-only coq-metacoq
make
