# The slam tactic

## Running

`./Isabelle2025/bin/isabelle jedit -d $SLAM -d $SLAM/tests -l Pure`

where `$SLAM` is the directory containing this README.

The subdirectory `tests/General` contains several examples of how to use the tactic.

See the file `slam_common.ML` for configuration options.

## Evaluation

### Mirabelle with Docker containers:

In the top level folder of the git repository run

`podman build --format=docker --no-cache --tag="mguerdi/isabelle-afp" --build-context slam-repo=. --file="evaluation/afp/Dockerfile" .`

`podman build --format=docker --no-cache --tag="mguerdi/isabelle-slam-patched" --build-context slam-repo=. --file="evaluation/slam_patched/Dockerfile" .`

#### Local (rootless docker)

OUTDATED

`docker run -v sledgehammer_cache:/home/isabelle/sledgehammer_cache -v mirabelle-log:/home/isabelle/mirabelle_output mguerdi/isabelle-slam-patched:latest mirabelle -j8 -O "~/mirabelle_output" -A 'sledgehammer[provers=zipperposition, fact_filter=mepo, slices=8, max_proofs=8, minimize=false, exhaustive_preplay=true, cache_dir="/home/isabelle/sledgehammer_cache"]' FFT`

The results are in `~/.local/share/docker/volumes/mirabelle-log/_data/mirabelle.log`.

#### Server (podman, rootless)

Create directories to mount as volumes

`mkdir ~/sledgehammer_output`
`mkdir ~/mirabelle_output`

Copy `mirabelle-long-run.log` containing the results of the Sledgehammer invocations to `mirabelle_output/`.

Run mirabelle:

`podman run --userns keep-id:uid=1000,gid=1000 -v ~/sledgehammer_cache:/home/isabelle/sledgehammer_cache -v ~/mirabelle_output:/home/isabelle/mirabelle_output mguerdi/isabelle-slam-patched:latest "slam metis"`

The results are in `~/mirabelle_output/mirabelle.log`.

Run on a specific theory, e.g. `Picks_Theorem`:

`podman run --userns keep-id:uid=1000,gid=1000 -v ~/sledgehammer_cache:/home/isabelle/sledgehammer_cache -v ~/mirabelle_output:/home/isabelle/mirabelle_output mguerdi/isabelle-slam-patched:latest "slam metis" Picks_Theorem`

### Analysis

The raw data are in the subdirectory `evaluation/analysis/runs`.

To analyze them and to generate plots, use `evaluation/analysis/main.py`.

Creating the plots requires the Python libraries `numpy` and `matplotlib` to be installed.

For example:

```
python main.py --plot-scatter --save-plot --dir runs/run46 --timeout-ms 4000
```

To get help with using the script, run `python main.py --help`.

