#!/usr/bin/python

import collections
import subprocess
import itertools
import re

session = "JEHA_TEST_GENERAL"

def sliding_window(iterable, n):
    "Collect data into overlapping fixed-length chunks or blocks."
    # sliding_window('ABCDEFG', 4) → ABCD BCDE CDEF DEFG
    iterator = iter(iterable)
    window = collections.deque(itertools.islice(iterator, n - 1), maxlen=n)
    for x in iterator:
        window.append(x)
        yield tuple(window)

# check=True raises an exception on non-zero exit code
output = subprocess.run([f"~/Isabelle2023/bin/isabelle build_log -v {session}"], shell=True, capture_output=True, check=True)

isabelle_messages = output.stdout.decode("utf-8").split("\n")

def get_filename_and_linenumber_and_elapsed_time(pair_of_lines):
    # Example output:
    # > Output (line 19 of "~/git/jeha/tests/Rules/sup.thy"):
    # > total elapsed time until contradiction: 38 ms
    if pair_of_lines[1].startswith("total elapsed time until contradiction:"):
        if not pair_of_lines[0].startswith("Output (line"):
            raise RuntimeError(f"{pair_of_lines[0]}\n{pair_of_lines[1]}")
        linenumber = int(''.join(itertools.takewhile(str.isdigit, pair_of_lines[0][13:])))
        filename_start_index = pair_of_lines[0].index("\"")
        filename_end_index = pair_of_lines[0].index("\"", filename_start_index+1)
        # this cuts of the two quotatino marks correctly
        filename = pair_of_lines[0][filename_start_index+1:filename_end_index]
        # cut of prefix and " ms" suffix
        time_in_ms = pair_of_lines[1][40:-3]
        return filename, linenumber, time_in_ms

for pair_of_lines in sliding_window(isabelle_messages, 2):
    result = get_filename_and_linenumber_and_elapsed_time(pair_of_lines)
    if result is not None:
        filename, linenumber, time = result
        print(filename, linenumber, time)

