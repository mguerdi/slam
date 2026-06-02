#!/bin/bash
set -euo pipefail
if [[ "$PWD" != "$(git rev-parse --show-toplevel)" ]]; then
  echo Run from top level of slam git repository. Exiting.
  exit 1
fi

if [[ $# -eq 1 ]]
then
  problems_file=$1
else
  problems_file=./evaluation/tptp/rating_zero_problems
  echo "No problems file supplied. Defaulting to $problems_file"
fi

commit=$(git rev-parse HEAD)
results_dir="./evaluation/analysis/tptp_runs/run$commit"
mkdir -p "$results_dir"
container_ids_file="$results_dir/container_ids"
if [[ -e "$container_ids_file" ]] && [[ ! -f "$container_ids_file" ]] || [[ -n $(cat "$container_ids_file") ]]
then
  echo "File $container_ids_file exists but is not regular or non-empty. Unfinished previous run? Exiting."
  exit 1
fi

problems_count=$(wc -l "$problems_file" | cut -d' ' -f1)
logical_cores=$(nproc --all)
# assume hyperthreading, leave two physical cores alone
max_procs=$((logical_cores / 2 - 2))
max_args=$((problems_count / max_procs))

xargs --arg-file="$problems_file" --max-procs=$max_procs --max-args=$max_args ./evaluation/tptp/run_tptp.sh "$results_dir"
