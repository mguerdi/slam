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

# # FIXME: use this instead of hg clone
# # 31b1c203357a (2025-01-08)
# # Look at Docker_Build.packages.mkString(" ")
# RUN curl "https://isabelle.sketis.net/repos/isabelle/archive/31b1c203357a.tar.gz"

RUN hg clone "https://isabelle-dev.sketis.net/source/isabelle/" Isabelle
# 31b1c203357a (2025-01-08)
RUN Isabelle/Admin/init -u -L -n -r 31b1c203357a

RUN hg clone "https://foss.heptapod.net/isa-afp/afp-devel"
# 01a5617ddb1f (2025-01-08)
RUN cd afp-devel && \
  hg update "01a5617ddb1f"

RUN Isabelle/bin/isabelle components -u "~/afp-devel/thys"

# Isabelle/Admin/init should take care of this
# RUN perl -pi -e 's,ISABELLE_HOME_USER=.*,ISABELLE_HOME_USER="\$USER_HOME/.isabelle",g;' Isabelle/etc/settings && \
#   perl -pi -e 's,ISABELLE_LOGIC=.*,ISABELLE_LOGIC=HOL,g;' Isabelle/etc/settings

ENTRYPOINT ["Isabelle/bin/isabelle"]
