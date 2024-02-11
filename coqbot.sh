git clone git@github.com:meta-introspector/metacoq.git --branch=coq-8.16
cd metacoq
git checkout 6c23b8f5649d7dc8f51bce9310a0b70a28607853
opam install --deps-only coq-metacoq
make
