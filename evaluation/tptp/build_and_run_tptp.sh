#!/bin/bash
set -euo pipefail
if [[ "$PWD" != "$(git rev-parse --show-toplevel)" ]]; then
  echo Run from top level of slam git repository. Exiting.
  exit 1
fi
./evaluation/tptp/build.sh
./evaluation/tptp/run_tptp.sh
