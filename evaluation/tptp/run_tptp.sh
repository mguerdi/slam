#!/bin/bash
if [[ "$PWD" != "$(git rev-parse --show-toplevel)" ]]; then
  echo Run from top level of slam git repository. Exiting.
  exit 1
fi
problems_file=./evaluation/tptp/rating_zero_problems
problems_count=$(wc -l $problems_file | cut -d' ' -f1)
logical_cores=$(nproc --all)
max_procs=$((logical_cores / 2 - 2))
max_args=$((problems_count / max_procs))
xargs --arg-file=$problems_file --max-procs=$max_procs --max-args=$max_args podman run --pids-limit=-1 --userns keep-id:uid=1000,gid=1000 -v ~/TPTP-v9.0.0:/home/isabelle/TPTP-v9.0.0:ro mguerdi/isabelle-slam-tptp tptp_slam_some
