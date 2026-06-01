#!/bin/bash
podman run --pids-limit=-1 --userns keep-id:uid=1000,gid=1000 -v ~/TPTP-v9.0.0:/home/isabelle/TPTP-v9.0.0:ro mguerdi/isabelle-slam-tptp tptp_slam_many ./git/slam/evaluation/tptp/rating_zero_problems
