git clone https://github.com/JasonGross/coq-ext-lib.git --branch=cumul
cd coq-ext-lib
opam pin add -y .
opam install -y -vv -t coq-quickchick
