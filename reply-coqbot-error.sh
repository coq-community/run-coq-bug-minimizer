#!/usr/bin/env bash

echo curl -X POST --data-urlencode "id=$1" --data-urlencode "filename=$2" --data-urlencode "error-log=@$3"
