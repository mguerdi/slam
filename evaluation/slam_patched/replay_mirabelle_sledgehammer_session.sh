#!/bin/bash
if [ $# -ne 2 ]
then
  echo "Wrong number of arguments. First argument needs to be the proof methods (space-separated, quoted), second argument the theory name"
  exit 1
fi
meths="$1"
thy="$2"
out_dir="$HOME/mirabelle_output/${thy}"
mkdir -p "${out_dir}"
cat "$HOME/mirabelle_output/mirabelle-long-run.log" > "${out_dir}/mirabelle.log"
"$HOME/Isabelle/bin/isabelle" mirabelle -o "threads=1" -t 60 -g 1 -O "${out_dir}" -A "sledgehammer_replay[provers=zipperposition, mini_preplay_inputs=true, proof_methods=\"${meths}\", instantiate=false, preplay_timeout=2, smt_proofs=false]" -X slow "${thy}"
