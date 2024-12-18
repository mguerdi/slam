FROM mguerdi/isabelle-afp-devel

USER root

RUN apt-get update && apt-get install -y \
  rsync \
  patch

USER isabelle
WORKDIR /home/isabelle/Isabelle


# copy jeha git repo to HOL source tree
COPY --chown=isabelle:isabelle . src/HOL/Tools/Jeha

RUN rm -rf src/HOL/Tools/Jeha/.git
RUN rm src/HOL/Tools/Jeha/.gitignore

# copy jeha.thy etc. to src/HOL/
RUN rsync -av src/HOL/Tools/Jeha/patches/Isabelle/ .
RUN hg add
RUN hg commit -m "copy jeha into isabelle-dev"

# RUN hg import -m "patch jeha dependency into Main" src/HOL/Tools/Jeha/patches/Isabelle/jeha_main.patch
# # From the changeset introducing dynamic registration of methods for sledgehammer
RUN hg import -m "dynamic registration of sledgehammer proof methods" src/HOL/Tools/Jeha/patches/Isabelle/dynamic_sledgehammer_isabelle_dev.patch
# Patch theory that registers jeha with sledgehammer into Main
RUN hg import -m "register jeha as dynamic sledgehammer proof method" src/HOL/Tools/Jeha/patches/Isabelle/jeha_sledgehammer_main.patch


WORKDIR /home/isabelle

RUN Isabelle/Admin/init -u -L -n

RUN Isabelle/bin/isabelle build -j12 Main

RUN mkdir mirabelle_output
