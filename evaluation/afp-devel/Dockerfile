# Dockerfile for afp-devel
# Based on https://hub.docker.com/r/makarius/isabelle

FROM mguerdi/isabelle-dev
SHELL ["/bin/bash", "-c"]

# Isabelle
WORKDIR /home/isabelle

# NOTE: Sync with
# * evaluation/slam-patched/Dockerfile
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
