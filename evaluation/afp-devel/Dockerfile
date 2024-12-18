# Dockerfile for isabelle-dev and afp-devel
# Based on https://hub.docker.com/r/makarius/isabelle

FROM ubuntu:22.04
SHELL ["/bin/bash", "-c"]

# packages
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get -y update && \
  apt-get install -y curl less libfontconfig1 libgomp1 openssh-client perl pwgen rlwrap mercurial && \
  apt-get clean

# user
RUN useradd -m isabelle && (echo isabelle:isabelle | chpasswd)
USER isabelle

# Isabelle
WORKDIR /home/isabelle

RUN hg clone "https://isabelle-dev.sketis.net/source/isabelle/" Isabelle
# This is the revision (from 2024-12-12) that the dynamic sledgehammer proof
# methods patch is based on.
# "81588:68dc8ffc94c246e13bb76a651b4e6ad73bc52981"
RUN Isabelle/Admin/init -u -L -n -r 68dc8ffc94c246e13bb76a651b4e6ad73bc52981

RUN hg clone "https://foss.heptapod.net/isa-afp/afp-devel"
# Checkout compatible revision of afp (2024-12-12)
RUN cd afp-devel && \
  hg update "8e4f2b00b851"

RUN Isabelle/bin/isabelle components -u "~/afp-devel/thys"

# Isabelle/Admin/init should take care of this
# RUN perl -pi -e 's,ISABELLE_HOME_USER=.*,ISABELLE_HOME_USER="\$USER_HOME/.isabelle",g;' Isabelle/etc/settings && \
#   perl -pi -e 's,ISABELLE_LOGIC=.*,ISABELLE_LOGIC=HOL,g;' Isabelle/etc/settings

ENTRYPOINT ["Isabelle/bin/isabelle"]
