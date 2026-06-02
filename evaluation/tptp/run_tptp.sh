#!/bin/bash
if [[ "$PWD" != "$(git rev-parse --show-toplevel)" ]]; then
  echo Run from top level of slam git repository. Exiting.
  exit 1
fi

if [[ $# -lt 1 ]]
then
  echo "This script takes at least one argument, the file to write container ids to. Exiting."
  echo "Got \$@="
  echo "$@"
  echo "instead"

  exit 1
fi
if [[ ! -f "$1" ]]
then
  echo "First argument must be a regular file. Exiting."
  exit 1
fi
container_ids_file="$1"
shift # discard first argument from $@

if [[ ! -d $TPTP ]]
then
  echo "TPTP environment variable must point to a directory. Exiting"
  exit 1
fi

# writes to `container_ids` shouldn't conflict: https://unix.stackexchange.com/a/346196
# --detach so the outer for loop can continue
podman run --detach --pids-limit=-1 --userns keep-id:uid=1000,gid=1000 -v "$TPTP":/home/isabelle/TPTP-v9.0.0:ro mguerdi/isabelle-slam-tptp tptp_slam_some "$@" >> "$container_ids_file"
