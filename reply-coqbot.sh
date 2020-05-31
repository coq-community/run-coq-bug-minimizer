#!/usr/bin/env bash

echo curl -X POST --data-urlencode "id=$1" --data-urlencode "filename=$2" --data-urlencode "minimized=@$3" --data-urlencode "build-log=@$4" --data-urlencode "minimization-log=@$5"
