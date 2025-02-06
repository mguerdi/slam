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

RUN hg import -m "dynamic sledgehammer methods, mirabelle caching" src/HOL/Tools/Jeha/patches/Isabelle/jeha_patches.patch

WORKDIR /home/isabelle

RUN Isabelle/Admin/init -u -L -n

# Main is the theory, HOL is the session
# TODO: use -a to build everything (How to exclude afp?)
# TODO: -o "threads=8" -j5 (server)
RUN Isabelle/bin/isabelle build -o "threads=8" -j2 -b HOL

# create mountpoint for mirabelle-log volume
RUN mkdir mirabelle_output

# create mountpoint for sledgehammer-cache volume
RUN mkdir sledgehammer_cache
