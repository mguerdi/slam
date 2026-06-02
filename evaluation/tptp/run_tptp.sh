#!/bin/bash
if [[ "$PWD" != "$(git rev-parse --show-toplevel)" ]]; then
  echo Run from top level of slam git repository. Exiting.
  exit 1
fi

if [[ $# -lt 1 ]]
then
  echo "This script takes at least one argument, the results directory. Exiting."
  exit 1
fi
if [[ ! -d "$1" ]]
then
  echo "First argument must be a directory. Exiting."
  exit 1
fi
results_dir="$1"
shift # discard first argument from $@

if [[ ! -d $TPTP ]]
then
  echo "TPTP environment variable must point to a directory. Exiting"
  exit 1
fi

# container_ids_file="$results_dir/container_ids"

# writes to `container_ids` shouldn't conflict: https://unix.stackexchange.com/a/346196
container_id=$(podman run --detach --pids-limit=-1 --userns keep-id:uid=1000,gid=1000 -v "$TPTP":/home/isabelle/TPTP-v9.0.0:ro mguerdi/isabelle-slam-tptp tptp_slam_some "$@")
# echo "$container_id" >> "$container_ids_file"

until [[ $(podman container inspect --format '{{.State.Running}}' "$container_id") = "false" ]]
do
  echo "Waiting for container ${container_id::12} to stop. Re-checking in 60 seconds."
  sleep 60
done

echo "Container ${container_id::12} to stopped, copying results."

podman cp "$container_id:results" "$results_dir/$container_id"
