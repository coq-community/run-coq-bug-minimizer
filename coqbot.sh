#!/usr/bin/env bash
git clone 'https://github.com/UniMath/UniMath'
cd UniMath
git checkout 75c3a38920088c3c5293ec3c1302cc67b3b8770e
make BUILD_COQ=no
coqc -noinit -type-in-type -indices-matter -w -notation-overridden -Q UniMath UniMath UniMath/Bicategories/OtherStructure/Examples/StructureOneTypes.v
