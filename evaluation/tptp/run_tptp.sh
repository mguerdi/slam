#!/bin/bash
podman run --userns keep-id:uid=1000,gid=1000 -v ~/TPTPv9.0.0:/home/isabelle/TPTPv9.0.0:readonly mguerdi/isabelle-slam-tptp ./git/evaluation/tptp/rating_zero_problems
