#!/bin/bash

if [[ $# -ne 1 ]]
then
  echo "This script exactly one argument. Exiting"
  exit 1
fi

if [[ ! -n $TPTP ]]
then
  echo "TPTP environment variable is not set."
  exit 1
fi

# export TPTP=/home/massin/research/tptp/TPTP-v9.0.0

echo Reading problems from "$1"
xargs --arg-file="$1" --max-procs=0 --max-args=1 ./run_on_problem.sh
