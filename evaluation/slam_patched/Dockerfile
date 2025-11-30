FROM mguerdi/isabelle-afp-devel

USER root

RUN apt-get update && apt-get install -y \
  rsync \
  patch

USER isabelle
WORKDIR /home/isabelle/Isabelle

# copy slam git repo to HOL source tree
COPY --chown=isabelle:isabelle . src/HOL/Tools/Slam

RUN rm -rf src/HOL/Tools/Slam/.git
RUN rm src/HOL/Tools/Slam/.gitignore

# copy slam.thy etc. to src/HOL/
RUN rsync -av src/HOL/Tools/Slam/patches/Isabelle/ .
RUN hg add
RUN hg commit -m "copy slam into isabelle-dev"

RUN hg import -m "dynamic sledgehammer methods, mirabelle caching" src/HOL/Tools/Slam/patches/Isabelle/slam_patches.patch

WORKDIR /home/isabelle

# create mountpoint for mirabelle-log volume
RUN mkdir mirabelle_output

# create mountpoint for sledgehammer-cache volume
RUN mkdir sledgehammer_cache

# copy in script for running mirabelle
COPY --chown=isabelle:isabelle ./evaluation/slam_patched/replay_mirabelle_sledgehammer_session.sh ./
RUN chmod u+x ./replay_mirabelle_sledgehammer_session.sh

RUN Isabelle/Admin/init -u -L -n

RUN Isabelle/bin/isabelle build -o "threads=8" -j4 -X slow -b -R Balog_Szemeredi_Gowers KD_Tree Descartes_Sign_Rule Nano_JSON PropResPI Noninterference_Ipurge_Unwinding Heard_Of Delta_System_Lemma Risk_Free_Lending Topological_Groups CubicalCategories Abstract-Hoare-Logics Separation_Algebra Riesz_Representation Buffons_Needle Constructive_Cryptography_CM Coppersmith_Method Falling_Factorial_Sum Finite_Fields Grothendieck_Schemes FOL-Fitting Quaternions DataRefinementIBP Sunflowers HOL-CSP SuperCalc Query_Optimization Picks_Theorem Banach_Steinhaus Rewrite_Properties_Reduction HyperHoareLogic ConcurrentGC Partial_Order_Reduction Chebyshev_Polynomials Saturation_Framework Marriage Well_Quasi_Orders Selection_Heap_Sort Matrix_Tensor Median_Method Stone_Kleene_Relation_Algebras Ergodic_Theory Lambda_Free_KBOs Transitive-Closure Relation_Algebra Nullstellensatz Hello_World Multirelations_Heterogeneous Progress_Tracking Sort_Encodings

ENTRYPOINT ["./replay_mirabelle_sledgehammer_session.sh"]
