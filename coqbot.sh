set -ex
opam install -y --deps-only coq-metacoq
printf -- git clone https://github.com/meta-introspector/metacoq.git --branch=feature/ltac_debug
git clone https://github.com/meta-introspector/metacoq.git --branch=feature/ltac_debug
cd metacoq
git checkout 6c23b8f5649d7dc8f51bce9310a0b70a28607853
make
