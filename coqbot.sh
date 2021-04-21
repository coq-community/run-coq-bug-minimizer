
git clone https://gitlab.mpi-sws.org/iris/iris.git && cd iris && git checkout 59d18188f9db844a75f5e37dc7cbc6c39ecbb24f
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
make builddep OPAMFLAGS=-y
make -j2 tests/one_shot.vo

