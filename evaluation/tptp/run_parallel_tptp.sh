#!/bin/bash
set -euo pipefail
if [[ "$PWD" != "$(git rev-parse --show-toplevel)" ]]; then
  echo Run from top level of slam git repository. Exiting.
  exit 1
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

problems_file=./evaluation/tptp/rating_zero_problems
problems_count=$(wc -l $problems_file | cut -d' ' -f1)
logical_cores=$(nproc --all)
# assume hyperthreading, leave two physical cores alone
max_procs=$((logical_cores / 2 - 2))
max_args=$((problems_count / max_procs))

xargs --arg-file=$problems_file --max-procs=$max_procs --max-args=$max_args ./evaluation/tptp/run_tptp.sh "$container_ids_file"

sleep 10 # allow all writes to container_ids_file to go through

# From now on we assume that all containers have started and their id has been written to container_ids_file.

all_stopped() {
  for container_id in $(cat "$container_ids_file")
  do
    if [[ $(podman container inspect --format '{{.State.Running}}' "$container_id") = "true" ]]
    then
      return 1
    fi
    return 0
  done
}

until all_stopped
do
  echo Waiting for all containers to start and stop. Re-checking in 30 seconds.
  sleep 30
done

for container_id in $(cat "$container_ids_file")
do
  podman cp "$container_id:results" "$results_dir/$container_id"
done
