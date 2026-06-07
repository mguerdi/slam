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

cidfile=$(mktemp)

done="false"
remaining_tries=5
until [[ $done = "true" ]] || [[ $remaining_tries -le 0 ]]
do
  if podman run --cidfile="$cidfile" --userns keep-id:uid=1000,gid=1000 -v "$TPTP":/home/isabelle/TPTP-v9.0.0:ro mguerdi/isabelle-slam-tptp tptp_slam_some "$@"
  then
    done="true"
    container_id=$(cat "$cidfile")
    if [[ -z $container_id ]]
    then
      printf "Container id wasn't written to cidfile. Can't find results for\n\t%s\nExiting.\n" "$@"
      exit 1
    fi
  else
    podman_exit_code=$?
    echo "Bad exit code $podman_exit_code from podman run."
    if [[ $podman_exit_code -eq 125 ]]; then
      # "error is with podman itself"
      : # no-op
    elif [[ $podman_exit_code -eq 126 ]]; then
      # "contained command cannot be invoked"
      exit 1
    elif [[ $podman_exit_code -eq 127 ]]; then
      # "contained command cannot be found"
      exit 1
    else
      # "contained command exit code"
      exit $podman_exit_code
    fi
    echo "Re-trying in 30 seconds. ($remaining_tries tries left)"
    remaining_tries=$((remaining_tries - 1))
    sleep 30
  fi
done

echo "Container ${container_id::12} to stopped, copying results."

podman cp "$container_id:results" "$results_dir/$container_id"
