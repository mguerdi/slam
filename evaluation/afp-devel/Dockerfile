# Dockerfile for afp-devel
# Based on https://hub.docker.com/r/makarius/isabelle

FROM mguerdi/isabelle-dev
SHELL ["/bin/bash", "-c"]

# Isabelle
WORKDIR /home/isabelle

RUN hg clone "https://foss.heptapod.net/isa-afp/afp-devel"
# NOTE: Sync with evaluation/isabelle-dev/Dockerfile
# 01a5617ddb1f (2025-01-08)
RUN cd afp-devel && \
  hg update "01a5617ddb1f"

RUN Isabelle/bin/isabelle components -u "~/afp-devel/thys"

# Isabelle/Admin/init should take care of this
# RUN perl -pi -e 's,ISABELLE_HOME_USER=.*,ISABELLE_HOME_USER="\$USER_HOME/.isabelle",g;' Isabelle/etc/settings && \
#   perl -pi -e 's,ISABELLE_LOGIC=.*,ISABELLE_LOGIC=HOL,g;' Isabelle/etc/settings

ENTRYPOINT ["Isabelle/bin/isabelle"]
