# The slam tactic

## Running

`./Isabelle2025/bin/isabelle jedit -d $SLAM -d $SLAM/tests -l Pure`

where `$SLAM` is the directory containing this README.

The subdirectory `tests/General` contains several examples of how to use the tactic.

See the file `slam_common.ML` for configuration options.

## Evaluation

### Mirabelle with Docker containers:

In the top level folder of the git repository run

`docker build --no-cache --tag="mguerdi/isabelle-afp" --file="evaluation/afp/Dockerfile" .`

`docker build --no-cache --tag="mguerdi/isabelle-slam-patched" --file="evaluation/slam_patched/Dockerfile" .`

#### Local (rootless docker)

`docker run -v sledgehammer_cache:/home/isabelle/sledgehammer_cache -v mirabelle-log:/home/isabelle/mirabelle_output mguerdi/isabelle-slam-patched:latest mirabelle -j8 -O "~/mirabelle_output" -A 'sledgehammer[provers=zipperposition, fact_filter=mepo, slices=8, max_proofs=8, minimize=false, exhaustive_preplay=true, cache_dir="/home/isabelle/sledgehammer_cache"]' FFT`

The results are in `~/.local/share/docker/volumes/mirabelle-log/_data/mirabelle.log`.

#### Server (without rootless docker)

Create directories to mount as volumes

`mkdir ~/sledgehammer_output`
`mkdir ~/mirabelle_output`

Make sure the user inside the docker container (e.g. uid=1000) can write into our user's (e.g. uid=1003) directories

`chmod a+w sledgehammer_output`
`chmod a+w mirabelle_output`

Run mirabelle

`docker run -v ~/sledgehammer_cache:/home/isabelle/sledgehammer_cache -v ~/mirabelle_log:/home/isabelle/mirabelle_output mguerdi/isabelle-slam-patched:latest mirabelle -j30 -O "~/mirabelle_output" -A 'sledgehammer[provers=zipperposition, fact_filter=mepo, slices=8, max_proofs=8, minimize=false, exhaustive_preplay=true, cache_dir="/home/isabelle/sledgehammer_cache"]' FFT`

The results are in `~/mirabelle_log/mirabelle.log`.

### Analysis

The raw data are in the subdirectory `evaluation/analysis/runs`.

To analyze them and to generate plots, use `evaluation/analysis/main.py`.

Creating the plots requires the Python libraries `numpy` and `matplotlib` to be installed.

For example:

```
python main.py --plot-scatter --save-plot --dir runs/run46 --timeout-ms 4000
```

To get help with using the script, run `python main.py --help`.

