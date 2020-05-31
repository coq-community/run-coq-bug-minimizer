opam install -y coq-ext-lib
eval $(opam env)
git clone https://github.com/satnam6502/oak-hardware
cd oak-hardware
git checkout 38971a7d0f8aa04b6fa4e21d1dfda3990ecf2c66
cd cava/cava
make coq
