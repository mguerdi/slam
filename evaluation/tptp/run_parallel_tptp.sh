#!/bin/bash
set -uo pipefail
if [[ "$PWD" != "$(git rev-parse --show-toplevel)" ]]; then
  echo Run from top level of slam git repository. Exiting.
  exit 1
fi

if [[ $# -eq 1 ]]
then
  problems_file=$1
else
  problems_file=./evaluation/tptp/higher_order_problems
  echo "No problems file supplied. Defaulting to $problems_file"
fi

commit=$(git rev-parse HEAD)
results_dir="./evaluation/analysis/tptp/runs/run$commit"
mkdir -p "$results_dir"

problems_count=$(wc -l "$problems_file" | cut -d' ' -f1)
logical_cores=$(nproc --all)

# For ~380 parallel containers, requires
#   kernel.keys.maxkeys=20000
#   kernel.keys.maxbytes=200000
# kernel parameters and
#   num_locks=2097152
# in containers.conf

# assume hyperthreading, leave two physical cores alone
max_procs=$((logical_cores / 2 - 2))
max_args=$((problems_count / max_procs))

ho_unification_strategies=(
  smash_flex_flex
  delay_flex_flex
  simpl_only
)

for ho_unification_strategy in "${ho_unification_strategies[@]}"
do
  echo RUNNING SLAM VARIANT "$ho_unification_strategy"
  xargs --arg-file="$problems_file" --max-procs=$max_procs --max-args=$max_args ./evaluation/tptp/run_tptp.sh "$results_dir" slam "$ho_unification_strategy"
  # FIXME: get rid of this once num_locks is set correctly
  echo REMOVING ALL STOPPED CONTAINERS
  podman container rm --all
done

for index in $(seq 0 25)
do
  echo RUNNING METIS VARIANT metis"$index"
  xargs --arg-file="$problems_file" --max-procs=$max_procs --max-args=$max_args ./evaluation/tptp/run_tptp.sh "$results_dir" metis "metis$index"
  # FIXME: get rid of this once num_locks is set correctly
  echo REMOVING ALL STOPPED CONTAINERS
  podman container rm --all
done
