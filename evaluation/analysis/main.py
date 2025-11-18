import argparse
from enum import Enum, auto
from functools import total_ordering
import os
import random
import math
import numpy as np


def str_digits(s):
    return "".join(c for c in s if c.isdigit())


def squeeze(line):
    # tr -s ' '
    return " ".join(part for part in line.split(" ") if len(part) > 0)


def is_replay_line(line):
    mirabelle_command = line.split(" ")[0]
    mirabelle_kind = line.split(" ")[1]
    return (
        "error: No mini preplay input for" not in line
        and mirabelle_command == "0.sledgehammer_replay"
        and mirabelle_kind not in ["finalize", "initialize"]
    )


# Terminology
#   call:    0.sledgehammer_replay goal.using 3492ms Sort_Encodings.T 393:13132 some Preplay: (metis intT_def protFw) (34 ms)
#   goal:                                            Sort_Encodings.T 393:13132
#   command:                                                                                  (metis intT_def protFw)
#   method:                                                                                    metis
#   result:                                                                                                           (34 ms)


@total_ordering
class ResultKind(Enum):
    # don't change: smaller is better
    SUCCESS = 0
    TIMEOUT = 1
    FAILED = 2

    @classmethod
    def from_string(cls, as_string):
        if "(failed)" == as_string:
            return cls.FAILED
        elif "timed out)" in as_string:
            return cls.TIMEOUT
        elif "s)" in as_string or "ms)" in as_string:
            return cls.SUCCESS
        else:
            raise ValueError(f'Can\'t turn "{as_string}" into ResultKind')

    def __lt__(self, other):
        if self.__class__ is other.__class__:
            return self.value < other.value
        raise NotImplementedError("Can only compare ResultKind with itself.")


def parse_time_ms(result_as_string):
    [time, unit] = result_as_string[1:-1].split(" ")
    time = float(time)
    if unit == "s":
        time_ms = time * 1000
    elif unit == "ms":
        time_ms = time
    else:
        raise ValueError(f"Can't parse {result_as_string} as time.")
    return time_ms


@total_ordering
class Result:
    def __init__(self, as_string, timeout_ms):
        self.as_string = as_string
        self.kind = ResultKind.from_string(as_string)
        if self.kind == ResultKind.SUCCESS:
            time_ms = parse_time_ms(as_string)
            if time_ms > timeout_ms:
                self.kind = ResultKind.TIMEOUT
            else:
                self.time_ms = time_ms

    def is_failed(self):
        return self.kind == ResultKind.FAILED

    def is_timeout(self):
        return self.kind == ResultKind.TIMEOUT

    def is_success(self):
        return self.kind == ResultKind.SUCCESS

    def __eq__(self, other):
        if self.__class__ == other.__class__:
            return self.kind == other.kind and self.time_ms == other.time_ms
        raise NotImplementedError("Can only compare Result to itself.")

    def __lt__(self, other):
        if self.__class__ == other.__class__:
            if self.kind == ResultKind.SUCCESS and other.kind == ResultKind.SUCCESS:
                return self.time_ms < other.time_ms
            return self.kind < other.kind


def parse_file(filename, timeout_ms):
    with open(filename) as f:
        s = f.read()
    lines = [
        squeezed for line in s.strip().split("\n") if is_replay_line(squeezed := squeeze(line))
    ]
    # print("\n".join(lines[:20]))
    calls = []
    for line in lines:
        # See "Terminology" above.
        goal = " ".join(line.split(" ")[3:5])
        tail = " ".join(line.split(" ")[7:])
        command = "(".join(tail.split("(")[:-1])
        if "slam" in command and "metis" in command:
            raise RuntimeError("Line has both slam and metis:\n" + line)
        if "slam" in command:
            method = "slam"
        elif "metis" in command:
            method = "metis"
        else:
            raise RuntimeError("Line has neither slam nor metis:\n" + line)
        result = Result("(" + (tail.split("(")[-1]), timeout_ms)
        calls.append({"goal": goal, "method": method, "command": command, "result": result})
    return calls


def best(calls):
    if len(calls) == 0:
        raise RuntimeError("Empty list of calls.")
    goal = calls[0]["goal"]
    best_call = calls[0]
    for call in calls:
        if call["goal"] != goal:
            raise RuntimeError("Calls don't all have the same goal.")
        if call["result"] < best_call["result"]:
            best_call = call
    return best_call


def group_by(dictionaries, key):
    grouped = {}
    for d in dictionaries:
        if d[key] in grouped:
            grouped[d[key]].append(d)
        else:
            grouped[d[key]] = [d]
    return grouped


def get_best_metis_by_goal(calls):
    calls_by_goal = group_by(calls, "goal")
    metis_calls_by_goal = {
        goal: [call for call in calls if call["method"] == "metis"]
        for goal, calls in calls_by_goal.items()
    }
    best_metis_by_goal = {
        goal: best(metis_calls) for goal, metis_calls in metis_calls_by_goal.items()
    }
    return best_metis_by_goal


def get_best_metis(calls):
    return list(get_best_metis_by_goal(calls).values())


def get_call_by_goal(calls, goal):
    for call in calls:
        if call["goal"] == goal:
            return call
    raise ValueError(f"No call with {goal} in calls.")


def summarize(calls, label, plot_cactus, plot_scatter, plot_hist, invocation):
    failed = [call for call in calls if call["result"].is_failed()]
    timed_out = [call for call in calls if call["result"].is_timeout()]
    success = [call for call in calls if call["result"].is_success()]

    # print(f"{len(failed)} calls failed")
    # print(f"{len(timed_out)} calls timed out")
    # print(f"{len(success)} calls succeeded")

    all_goals = set(call["goal"] for call in calls)
    success_goals = set(call["goal"] for call in success)
    always_failed_or_timed_out_goals = all_goals - success_goals

    print(f"{len(all_goals)} goals in total")
    print(f"{len(always_failed_or_timed_out_goals)} goals failed or timed out (all calls)")
    print(f"{len(success_goals)} goals succeeded")

    slam_calls = [call for call in calls if call["method"] == "slam"]

    slam_fails = [call["goal"] for call in slam_calls if call["result"].is_failed()]
    slam_timeouts = [call["goal"] for call in slam_calls if call["result"].is_timeout()]
    slam_success = [call["goal"] for call in slam_calls if call["result"].is_success()]

    slam_fails_or_timeouts = slam_fails + slam_timeouts

    # print(slam_success[0])
    # print(slam_fails)

    # From now on "metis" means the best-performing metis variant for any particular goal.
    metis_calls = get_best_metis(calls)

    metis_fails = [call["goal"] for call in metis_calls if call["result"].is_failed()]
    metis_timeouts = [call["goal"] for call in metis_calls if call["result"].is_timeout()]
    metis_success = [call["goal"] for call in metis_calls if call["result"].is_success()]

    metis_fails_or_timeouts = metis_fails + metis_timeouts

    # print(metis_any_success[0])
    print(f"slam fails: {len(slam_fails)}")
    print(f"slam timeouts: {len(slam_timeouts)}")
    print(f"slam success: {len(slam_success)}")
    print(f"metis fails (no variant worked): {len(metis_fails)}")
    print(f"metis timeouts (no variant worked): {len(metis_timeouts)}")
    print(f"metis success (any variant worked): {len(metis_success)}")

    slam_success_metis_fail_or_timeout = set(slam_success) - set(metis_success)

    print(f"slam success, metis fail or timeout: {str(len(slam_success_metis_fail_or_timeout))}")

    print(
        "\n".join(
            [
                get_call_by_goal(slam_calls, goal)["result"].as_string + "\t\t" + goal
                for goal in slam_success_metis_fail_or_timeout
            ]
        )
    )

    # print(slam_success_metis_fail_or_timeout)
    # print(sorted(list(slam_success_metis_fail_or_timeout))[:10])

    metis_success_slam_fail_or_timeout = set(metis_success) - set(slam_success)
    print(f"metis success, slam fail or timeout: {str(len(metis_success_slam_fail_or_timeout))}")
    print("10 easiest (to metis) problems where slam fails:")
    ten_easiest = sorted(
        list(metis_success_slam_fail_or_timeout),
        key=lambda goal: get_call_by_goal(metis_calls, goal)["result"],
    )[:10]
    print("\n".join(ten_easiest))

    if plot_cactus:
        plot_success_calls(metis_calls, slam_calls, label, invocation)

    both_success = list(set(metis_success).intersection(set(slam_success)))
    # get_call_by_goal(slam_calls, goal)["result"].as_string + "\t\t" + goal
    slam_both_success_times = [
        get_call_by_goal(slam_calls, goal)["result"].time_ms for goal in both_success
    ]
    metis_both_success_times = [
        get_call_by_goal(metis_calls, goal)["result"].time_ms for goal in both_success
    ]

    log_slam_both_success_times = np.log(slam_both_success_times)
    log_metis_both_success_times = np.log(metis_both_success_times)

    polyfit_degree = 1
    fit = np.polyfit(log_metis_both_success_times, log_slam_both_success_times, polyfit_degree)
    def extrapolate(time):
        return np.exp(np.sum([fit[i] * np.log(time)**(polyfit_degree - i) for i in range(polyfit_degree + 1)]))
    polyfit_label = " + ".join(f"{fit[i]:.2f} x**{polyfit_degree - i}" for i in range(polyfit_degree + 1))

    metis_success_slam_fail_or_timeout_times = [
        get_call_by_goal(metis_calls, goal)["result"].time_ms
        for goal in metis_success_slam_fail_or_timeout
    ]
    slam_fake_long_times = len(metis_success_slam_fail_or_timeout_times) * [8000.0]
    random.seed()
    slam_fake_random_times = [
        random.random() * 3000 + 10000 for _ in metis_success_slam_fail_or_timeout_times
    ]
    # slam_fake_extrapolated_times = [time**2.16 for time in metis_success_slam_fail_or_timeout_times]
    slam_fake_extrapolated_times = [
        extrapolate(time) for time in metis_success_slam_fail_or_timeout_times
    ]

    slam_success_metis_fail_or_timeout_times = [
        get_call_by_goal(slam_calls, goal)["result"].time_ms
        for goal in slam_success_metis_fail_or_timeout
    ]

    # slam_vs_metis_slowdown = [get_call_by_goal(slam_calls, goal)["result"].time_ms / get_call_by_goal(metis_calls, goal)["result"].time_ms for goal in both_success]
    # slam_vs_metis_slowdown = sorted(slam_vs_metis_slowdown)

    max_time = max(np.max(slam_both_success_times), np.max(metis_both_success_times))

    hist_log_bins = np.logspace(np.log(1), np.log(max_time), num=50, base=np.e)

    metis_better = sum(1 for (metis_time, slam_time) in zip(metis_both_success_times, slam_both_success_times) if metis_time < slam_time)
    slam_better = sum(1 for (slam_time, metis_time) in zip(slam_both_success_times, metis_both_success_times) if slam_time < metis_time)
    print("METIS BETTER:", metis_better)
    print("SLAM BETTER:", slam_better)

    if plot_scatter:
        plt.rc("axes", axisbelow=True)
        plt.grid(True, which="major", color="0.65")

        cm = plt.get_cmap('nipy_spectral')
        color = cm(((135 * (invocation + 1)) % 360) / 360.)
        plt.scatter(metis_both_success_times, slam_both_success_times, c=color, marker=".", label=label, s=1, alpha=0.5)

        # plt.scatter(metis_both_success_times, [extrapolate(time) for time in metis_both_success_times], marker='.')
        # plt.scatter(metis_success_slam_fail_or_timeout_times, slam_fake_long_times, marker='x')
        # plt.scatter(metis_success_slam_fail_or_timeout_times, slam_fake_random_times, marker='x')
        
        min_time_minus = .4
        max_time_plus = max_time / .4

        plt.plot([min_time_minus, max_time_plus], [min_time_minus, max_time_plus], color="red", label="diagonal")
        # plt.plot(metis_success_slam_fail_or_timeout_times, slam_fake_extrapolated_times, c=color, label=polyfit_label)
        plt.xlim(min_time_minus, max_time_plus)
        plt.ylim(min_time_minus, max_time_plus)
        print("MAX TIME", max_time)


    if plot_hist:
        plt.hist(
            metis_both_success_times,
            hist_log_bins,
            histtype="step",
            label=label + " metis times (both successful)",
        )
        plt.hist(
            slam_both_success_times,
            hist_log_bins,
            histtype="step",
            label=label + " slam times (both successful)",
        )
        plt.hist(
            metis_success_slam_fail_or_timeout_times,
            hist_log_bins,
            histtype="step",
            label=label + " metis times (only metis successful)",
        )
        plt.hist(
            slam_success_metis_fail_or_timeout_times,
            hist_log_bins,
            histtype="step",
            label=label + " slam times (only slam successful)",
        )


def plot_success_calls(metis_calls, slam_calls, label, invocation):
    cm = plt.get_cmap('nipy_spectral')
    color = cm(((135 * invocation) % 360) / 360.)

    def plot_calls(calls, label):
        success = sorted(
            [call for call in calls if call["result"].is_success()], key=lambda call: call["result"]
        )
        success_times = [call["result"].time_ms for call in success]
        cumulative_problems = [i for i, _ in enumerate(success)]
        # print(f"plotting with label {label}")
        plt.plot(success_times, cumulative_problems, "+", color=color, label=label)
        # print("done plotting")

    plot_calls(metis_calls, label=label + " (metis)")
    plot_calls(slam_calls, label=label + " (slam)")


# https://stackoverflow.com/questions/38834378/path-to-a-directory-as-argparse-argument
def dir_path(string):
    if os.path.isdir(string):
        return string
    else:
        raise NotADirectoryError(string)


if __name__ == "__main__":
    # CLI
    parser = argparse.ArgumentParser(prog="metis vs slam analysis script")
    parser.add_argument(
        "-d",
        "--dir",
        action="append",
        help="directory containing the files `commit` and `mirabelle.log`",
        type=dir_path,
    )
    parser.add_argument("-pc", "--plot-cactus", action="store_true", help="create cactus plot")
    parser.add_argument("-ps", "--plot-scatter", action="store_true", help="create scatter plot")
    parser.add_argument("-ph", "--plot-hist", action="store_true", help="create histograms")
    parser.add_argument("-s", "--save-plot", action="store_true", help="save plot to file")
    parser.add_argument(
        "-t",
        "--timeout-ms",
        type=int,
        default=4000,
        help="consider all calls above this threshold (in ms) as timeouts",
    )
    args = parser.parse_args()

    if sum(bool(arg) for arg in (args.plot_cactus, args.plot_scatter, args.plot_hist)) > 1:
        raise RuntimeError("specify at most one of --plot-cactus, --plot-scatter and --plot-hist")

    plot_any = args.plot_cactus or args.plot_scatter or args.plot_hist
    if plot_any:
        import matplotlib
        from matplotlib import pyplot as plt

        plt.rc("axes", axisbelow=True)
        rc_fonts = {
            "font.family": "serif",
            "font.size": 10 if args.save_plot else 20,
            'figure.figsize': (5, 3),
            "text.usetex": True,
            'text.latex.preamble':
                r"""
                \usepackage{libertine}
                \usepackage[libertine]{newtxmath}
                """,
        }
        matplotlib.rcParams.update(rc_fonts)
        
        plt.subplots(figsize=(4.5, 4.5)) # inches

    if args.dir is not None:
        if isinstance(args.dir, list):
            runs_dirs = args.dir
        elif isinstance(args.dir, str):
            runs_dirs = [args.dir]
        else:
            raise TypeError(f"neither string nor list of strings: {args.dir=}")
    else:
        if not os.path.isdir("runs"):
            raise RuntimeError("Couldn't find directory with name 'runs'.")
        runs_dirs_relative = sorted(
            list(os.listdir("runs")), key=lambda dir_name: int(str_digits(dir_name))
        )
        runs_dirs = ["runs/" + dirname for dirname in runs_dirs_relative]

    for i, dirname in enumerate(runs_dirs):
        filename = dirname + "/mirabelle.log"
        try:
            with open(dirname + "/commit") as c:
                commit = c.read()[:7]
        except FileNotFoundError as e:
            commit = "UNKOWN_COMMIT"
        print(filename, commit)
        try:
            calls = parse_file(filename, args.timeout_ms)
            label = dirname + " " + commit
            # label = "commit " + commit
            summarize(
                calls, label, args.plot_cactus, args.plot_scatter, args.plot_hist, i
            )
        except FileNotFoundError:
            print(f"skipping {filename} (not found)")
        print()

    if args.plot_cactus:
        plt.xlabel("time [ms]")
        plt.ylabel("number of goals solved")
        plt.legend()
        # plt.title("metis vs. slam")

    if args.plot_scatter:
        plt.xscale("log")
        plt.yscale("log")

        plt.xlabel("metis time [ms]")
        plt.ylabel("slam time [ms]")
        plt.legend()
        # plt.title("metis vs. slam times")

    if args.plot_hist:
        plt.xscale("log")
        plt.xlabel("time [ms]")
        plt.ylabel("count")
        plt.legend()
        # plt.title("histograms")

    if plot_any:
        if args.save_plot:
            plt.savefig("plot.pdf")
        else:
            plt.show()
