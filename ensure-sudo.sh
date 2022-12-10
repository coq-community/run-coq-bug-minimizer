#!/usr/bin/env bash

set -x

if ! command -v sudo &> /dev/null; then
    echo '::group::install sudo'
    su -c 'apt-get update -y'
    su -c 'apt-get install -y sudo'
    echo '::endgroup::'
fi
