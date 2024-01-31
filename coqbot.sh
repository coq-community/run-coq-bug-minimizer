#!/usr/bin/env bash
cat > thebug.v <<'EOF'
git clone 'https://github.com/UniMath/UniMath'
cd UniMath
make BUILD_COQ=no
coqc -noinit -type-in-type -indices-matter -w -notation-overridden -Q UniMath UniMath UniMath/Bicategories/OrthogonalFactorization/EsoFactorizationSystem.vo
EOF
coqc -q thebug.v
