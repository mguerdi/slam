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
RUN patch -p1 < src/HOL/Tools/Jeha/patches/Isabelle/Main.patch
# RUN patch -p1 < src/HOL/Tools/Jeha/patches/Isabelle/jeha_isabelle_2024.patch

WORKDIR /home/isabelle
