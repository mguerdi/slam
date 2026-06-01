#!/bin/bash
set -euo pipefail
if [[ "$PWD" != "$(git rev-parse --show-toplevel)" ]]; then
  echo Run from top level of slam git repository. Exiting.
  exit 1
fi
podman build --format=docker --tag="mguerdi/isabelle-slam-tptp" --build-context slam-repo=. --file="evaluation/slam_tptp/Dockerfile"
./evaluation/tptp_slam/run_tptp.sh
echo DONE
