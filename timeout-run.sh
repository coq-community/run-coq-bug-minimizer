#!/usr/bin/env bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
# use 5h15m as the timeout; the timeout for this stage is 5h30m, so we leave a generous allotment for docker
timeout 18900 "$DIR/run.sh"
