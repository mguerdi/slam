#!/bin/bash
if [[ "$PWD" != "$(git rev-parse --show-toplevel)" ]]; then
  echo Run from top level of slam git repository. Exiting.
  exit 1
fi

if [[ $# -lt 2 ]]
then
  echo "This script takes at least two arguments, the results directory and the prover. Exiting."
  exit 1
fi
if [[ ! -d "$1" ]]
then
  echo "First argument must be a directory. Exiting."
  exit 1
fi
results_dir="$1"
prover=$2
shift 2 # discard first two arguments from $@

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
  if podman run --cidfile="$cidfile" --userns keep-id:uid=1000,gid=1000 -v "$TPTP":/home/isabelle/TPTP-v9.0.0:ro mguerdi/isabelle-slam-tptp "tptp_${prover}_some" "$@"
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
    if [[ $podman_exit_code -eq 125 ]]; then
      # "error is with podman itself"
      # happens when
      # Error: allocating lock for new container: allocation failed; exceeded num_locks (2048)
      # Fix: change num_locks in podman config and run podman `system renumber`.
      echo "Bad exit code $podman_exit_code from podman run. Exiting with 127."
      exit 127
    elif [[ $podman_exit_code -eq 126 ]]; then
      # "contained command cannot be invoked"
      # happens when
      # Error: OCI runtime error: crun: create keyring `...`: Disk quota exceeded
      echo "Bad exit code $podman_exit_code from podman run."
      : # no-op
    elif [[ $podman_exit_code -eq 127 ]]; then
      # "contained command cannot be found"
      echo "Bad exit code $podman_exit_code from podman run. Exiting with 127."
      exit 127
    else
      # "contained command exit code"
      echo "Bad exit code $podman_exit_code from contained command. Exiting with 1."
      exit 1
    fi
    echo "Re-trying in 30 seconds. ($remaining_tries tries left)"
    remaining_tries=$((remaining_tries - 1))
    sleep 30
  fi
done

echo "Container ${container_id::12} to stopped, copying results."

podman cp "$container_id:results" "$results_dir/$container_id"
