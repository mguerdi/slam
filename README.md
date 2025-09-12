# The slam tactic

## Running

`./Isabelle2025/bin/isabelle jedit -d $SLAM -d $SLAM/tests -l Pure`

where `$SLAM` is the directory containing this README.

The subdirectory `tests/General` contains several examples of how to use the tactic.

## Evaluation

The raw data are in the subdirectory `evaluation/analysis/runs`.

To analyze them and to generate plots, use `evaluation/analysis/main.py`.

Creating the plots requires the Python libraries `numpy` and `matplotlib` to be installed.

To reproduce the plot from the paper, for example:

```
python main.py --plot-scatter --save-plot --dir runs/run46 --timeout-ms 4000
```

To get help with using the script, run `python main.py --help`.

