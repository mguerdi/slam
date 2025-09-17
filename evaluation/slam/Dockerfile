FROM mguerdi/isabelle-afp

USER isabelle
WORKDIR /home/isabelle

COPY --chown=isabelle:isabelle . slam
RUN Isabelle/bin/isabelle components -u "~/slam"
