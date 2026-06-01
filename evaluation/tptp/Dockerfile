# Dockerfile for afp-devel
# Based on https://hub.docker.com/r/makarius/isabelle

FROM mguerdi/isabelle-dev
SHELL ["/bin/bash", "-c"]

# Isabelle
USER isabelle
WORKDIR /home/isabelle

RUN Isabelle/Admin/init -u -L -n

RUN Isabelle/bin/isabelle build -o "threads=8" -j10 HOL-TPTP

# copy slam git repo
COPY --from=slam-repo --chown=isabelle:isabelle . ./git/slam

RUN Isabelle/bin/isabelle components -u ./git/slam/slam_tptp

RUN mkdir TPTP-v9.0.0

ENV TPTP=/home/isabelle/TPTP-v9.0.0

ENTRYPOINT ["Isabelle/bin/isabelle"]
