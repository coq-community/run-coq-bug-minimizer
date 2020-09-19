opam install -y coq.8.11 coq-ext-lib
eval $(opam env)

mkdir temp
cd temp
wget https://github.com/coq/coq/files/4698509/bug.v.zip
unzip bug.v.zip
coqc -q bug.v
#git clone https://github.com/satnam6502/oak-hardware
#cd oak-hardware
#git checkout 38971a7d0f8aa04b6fa4e21d1dfda3990ecf2c66
#cd cava/cava
#make coq
