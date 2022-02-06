opam install -y coq.8.7.2
eval $(opam env)
git clone git@github.com:alizter/VST.git
cd VST
git checkout test-6984
make veric/SeparationLogic.vo
