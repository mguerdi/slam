FROM mguerdi/isabelle-afp

USER root

RUN apt-get update && apt-get install -y \
  rsync \
  patch

USER isabelle
WORKDIR /home/isabelle/Isabelle

# copy jeha git repo to HOL source tree
COPY --chown=isabelle:isabelle . src/HOL/Tools/Jeha
RUN rsync -av src/HOL/Tools/Jeha/patches/Isabelle/ .
# Patch jeha dependency into Main
RUN patch -p1 < src/HOL/Tools/Jeha/patches/Isabelle/jeha_main.patch
# From the changeset introducing dynamic registration of methods for sledgehammer
RUN patch -p1 < src/HOL/Tools/Jeha/patches/Isabelle/dynamic_sledgehammer.patch
# Patch theory that registers jeha with sledgehammer into Main
RUN patch -p1 < src/HOL/Tools/Jeha/patches/Isabelle/jeha_sledgehammer_main.patch
# Changes for isabelle 2024
# RUN patch -p1 < src/HOL/Tools/Jeha/patches/Isabelle/jeha_isabelle_2024.patch

WORKDIR /home/isabelle

RUN Isabelle/bin/isabelle build -j12 Main

RUN mkdir mirabelle_output
