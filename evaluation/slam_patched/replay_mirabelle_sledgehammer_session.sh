#!/bin/bash
mkdir -p "$HOME/mirabelle_output/$1"
cat "$HOME/mirabelle_output/mirabelle-long-run.log" > "$HOME/mirabelle_output/$1/mirabelle.log"
"$HOME/Isabelle/bin/isabelle" mirabelle -o "threads=1" -g 1 -O "$HOME/mirabelle_output/$1" -A 'sledgehammer_replay[provers=zipperposition, mini_preplay_inputs=true, proof_methods="metis slam", instantiate=false, preplay_timeout=2, smt_proofs=false]' -X slow "$1"
