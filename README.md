# Evaluation

## Mirabelle

`~/Isabelle2023/bin/isabelle mirabelle -d ~/git/jeha -d ~/git/jeha/tests -O ~/mirabelle_output -A jeha -s 1 -t 60 -T misc JEHA_TEST_GENERAL`

## Mirabelle with Docker containers:

In the top level folder of the git repository run

`docker build --no-cache --tag="mguerdi/isabelle-afp" --file="evaluation/afp/Dockerfile" .`

`docker build --no-cache --tag="mguerdi/isabelle-jeha-patched" --file="evaluation/jeha_patched/Dockerfile" .`

### Local (rootless docker)

`docker run -v sledgehammer_cache:/home/isabelle/sledgehammer_cache -v mirabelle-log:/home/isabelle/mirabelle_output mguerdi/isabelle-jeha-patched:latest mirabelle -j8 -O "~/mirabelle_output" -A 'sledgehammer[provers=zipperposition, fact_filter=mepo, slices=8, max_proofs=8, minimize=false, exhaustive_preplay=true, cache_dir="/home/isabelle/sledgehammer_cache"]' FFT`

The results are in `~/.local/share/docker/volumes/mirabelle-log/_data/mirabelle.log`.

### Server (without rootless docker)

Create directories to mount as volumes

`mkdir ~/sledgehammer_output`
`mkdir ~/mirabelle_output`

Make sure the user inside the docker container (e.g. uid=1000) can write into our user's (e.g. uid=1003) directories

`chmod a+w sledgehammer_output`
`chmod a+w mirabelle_output`

Run mirabelle

`docker run -v ~/sledgehammer_cache:/home/isabelle/sledgehammer_cache -v ~/mirabelle_log:/home/isabelle/mirabelle_output mguerdi/isabelle-jeha-patched:latest mirabelle -j30 -O "~/mirabelle_output" -A 'sledgehammer[provers=zipperposition, fact_filter=mepo, slices=8, max_proofs=8, minimize=false, exhaustive_preplay=true, cache_dir="/home/isabelle/sledgehammer_cache"]' FFT`

The results are in `~/mirabelle_log/mirabelle.log`.

## Compare Metis and Jeha

FIXME

To test on the theory FFT (chosen for no particular reason) use `dynamic_sledgehammer_without_prefer_dynamic.patch` with:

`docker run -v mirabelle-log:/home/isabelle/mirabelle_output mguerdi/isabelle-jeha-patched:latest mirabelle -j10 -O "~/mirabelle_output" -A "sledgehammer[provers=zipperposition, fact_filter=mepo, slices=8, max_proofs=8, minimize=false, exhaustive_preplay=true]" -s 50 FFT`

Results of these two calls are in `./evaluation/test_fft`
