#!/bin/bash
set -euo pipefail
if [[ "$PWD" != "$(git rev-parse --show-toplevel)" ]]; then
  echo Run from top level of slam git repository. Exiting.
  exit 1
fi
commit=$(git rev-parse HEAD)
results_dir="$HOME/analysis/runs/run$commit"
mkdir -p "$results_dir"
echo "$commit" > "$results_dir/commit"
if [ ! -f "$HOME"/mirabelle_output/mirabelle-long-run.log ]; then
    echo "$HOME"/mirabelle_output/mirabelle-long-run.log not found. Consult README. Exiting.
    exit 1
fi
if ! [[ -z $(podman container ls -q) ]]; then
  echo There are running containers. Exiting.
  exit 1
fi
podman build --format=docker --no-cache --tag="mguerdi/isabelle-slam-patched" --build-context slam-repo=. --file="evaluation/slam_patched/Dockerfile"
podman run --userns keep-id:uid=1000,gid=1000 -v ~/sledgehammer_cache:/home/isabelle/sledgehammer_cache -v ~/mirabelle_output:/home/isabelle/mirabelle_output mguerdi/isabelle-slam-patched:latest "slam metis"
cp -r "$HOME/mirabelle_output" "$results_dir/mirabelle_output"
