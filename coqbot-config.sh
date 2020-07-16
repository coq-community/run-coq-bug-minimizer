#!/usr/bin/env bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

export nl=$'\n'
export start_code='```'"${nl}"
export start_coq_code='```coq'"${nl}"
export end_code="${nl}"'```'
export COQBOT_URL=''
