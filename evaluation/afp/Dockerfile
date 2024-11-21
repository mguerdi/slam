FROM makarius/isabelle:Isabelle2023

USER root

RUN apt-get update && apt-get install -y \
  mercurial

USER isabelle
WORKDIR /home/isabelle

RUN hg clone "https://foss.heptapod.net/isa-afp/afp-2023"

RUN Isabelle/bin/isabelle components -u "~/afp-2023/thys"

# install missing components (hugo, ...)
#   https://mailman46.in.tum.de/pipermail/isabelle-dev/2012-October/011712.html
RUN Isabelle/bin/isabelle components -a
