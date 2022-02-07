opam switch create coq.8.7.2 --empty
opam switch coq.8.7.2
opam install -y coq.8.7.2
eval $(opam env)
git clone https://github.com/Alizter/VST.git
cd VST
git checkout test-6984
make veric/SeparationLogic.vo
