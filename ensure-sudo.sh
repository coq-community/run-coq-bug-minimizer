#!/usr/bin/env bash

set -x

if ! command -v sudo &> /dev/null; then
    printf '::group::install sudo\n'
    su -c 'apt-get update -y'
    su -c 'apt-get install -y sudo'
    printf '::endgroup::\n'
fi
