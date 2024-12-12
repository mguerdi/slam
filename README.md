# Evaluation

## Mirabelle

`~/Isabelle2023/bin/isabelle mirabelle -d ~/git/jeha -d ~/git/jeha/tests -O ~/mirabelle_output -A jeha -s 1 -t 60 -T misc JEHA_TEST_GENERAL`

## Mirabelle with Docker containers:

In the top level folder of the git repository run

`docker build --tag="mguerdi/isabelle-afp" --file="evaluation/afp/Dockerfile" .`

`docker build --tag="mguerdi/isabelle-jeha-patched" --file="evaluation/jeha_patched/Dockerfile" .`

`docker run -v mirabelle-log:/home/isabelle/mirabelle_output mguerdi/isabelle-jeha-patched:latest mirabelle -j12 -O "~/mirabelle_output" -A "sledgehammer[provers = zipperposition, timeout = 10]" FFT`

The results are in `view ~/.local/share/docker/volumes/mirabelle-log/_data/mirabelle.log`.

## Compare Metis and Jeha

To test on the theory FFT (chosen for no particular reason) use `dynamic_sledgehammer_without_prefer_dynamic.patch` with:

`docker run -v mirabelle-log:/home/isabelle/mirabelle_output mguerdi/isabelle-jeha-patched:latest mirabelle -j10 -O "~/mirabelle_output" -A "sledgehammer[provers=zipperposition, exhaustive_preplay=true, proof_method=jeha]" FFT`

`docker run -v mirabelle-log:/home/isabelle/mirabelle_output mguerdi/isabelle-jeha-patched:latest mirabelle -j10 -O "~/mirabelle_output" -A "sledgehammer[provers=zipperposition, exhaustive_preplay=true, proof_method=metis]" FFT`

Results of these two calls are in `./evaluation/test_fft`
