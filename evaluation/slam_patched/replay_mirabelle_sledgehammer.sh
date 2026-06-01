#!/bin/bash
# run this on the server
if [ $# -ne 0 ]
then
  echo "This script takes no arguments. Exiting"
  exit 1
fi
echo "Balog_Szemeredi_Gowers KD_Tree Descartes_Sign_Rule Nano_JSON PropResPI Noninterference_Ipurge_Unwinding Heard_Of Delta_System_Lemma Risk_Free_Lending Topological_Groups Abstract-Hoare-Logics Separation_Algebra Riesz_Representation Buffons_Needle Constructive_Cryptography_CM Coppersmith_Method Falling_Factorial_Sum Finite_Fields Grothendieck_Schemes FOL-Fitting Quaternions DataRefinementIBP Sunflowers HOL-CSP SuperCalc Query_Optimization Picks_Theorem Banach_Steinhaus Rewrite_Properties_Reduction HyperHoareLogic ConcurrentGC Chebyshev_Polynomials Saturation_Framework Marriage Well_Quasi_Orders Selection_Heap_Sort Matrix_Tensor Median_Method Stone_Kleene_Relation_Algebras Ergodic_Theory Lambda_Free_KBOs Transitive-Closure Relation_Algebra Nullstellensatz Hello_World Multirelations_Heterogeneous Progress_Tracking Sort_Encodings" | xargs -n 1 -P 50 podman run --userns keep-id:uid=1000,gid=1000 -v ~/sledgehammer_cache:/home/isabelle/sledgehammer_cache -v ~/mirabelle_output:/home/isabelle/mirabelle_output mguerdi/isabelle-slam-patched:latest "slam metis"
