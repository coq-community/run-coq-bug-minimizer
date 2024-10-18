opam pin add -y --no-action 'git+https://github.com/womeier/wasmcert-coq.git#ce5f3abb5d290cfb25addd5eb1a245e8d7b8aaaf'
opam pin add -y --no-action 'git+https://github.com/womeier/certicoqwasm#master'
opam install -y --confirm-level=unsafe-yes coq-wasm coq-certicoq
find /home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/
cat > test_bug.v <<EOF
Require Wasm.binary_format_parser.

Declare ML Module "coq-certicoq.plugin".
Import Wasm.binary_format_parser.
Import Wasm.datatypes.
Definition test_bytes : list Byte.byte.
Admitted.
Definition test_module : option module.
exact (run_parse_module test_bytes).
Defined.

CertiCoq Compile test_module.
EOF
coqc -q test_bug.v
