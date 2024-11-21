FROM mguerdi/isabelle-afp

USER isabelle
WORKDIR /home/isabelle

COPY --chown=isabelle:isabelle . jeha
RUN Isabelle/bin/isabelle components -u "~/jeha"
