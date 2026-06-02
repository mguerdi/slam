# Dockerfile for afp-devel
# Based on https://hub.docker.com/r/makarius/isabelle

FROM mguerdi/isabelle-dev
SHELL ["/bin/bash", "-c"]

# Isabelle
USER isabelle
WORKDIR /home/isabelle

# 58aa74c02516 (2026-01-21)
RUN Isabelle/Admin/init -u -L -n -r 58aa74c02516

RUN Isabelle/bin/isabelle build -o "threads=4" -j10 HOL-TPTP

# copy slam git repo
COPY --from=slam-repo --chown=isabelle:isabelle . ./git/slam

RUN Isabelle/bin/isabelle components -u ./git/slam
RUN Isabelle/bin/isabelle components -u ./git/slam/slam_tptp

RUN Isabelle/bin/isabelle build -o "threads=4" -j1 SLAM_TPTP

RUN mkdir TPTP-v9.0.0

ENV TPTP=/home/isabelle/TPTP-v9.0.0

ENTRYPOINT ["Isabelle/bin/isabelle"]
