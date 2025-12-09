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


# "Session"
def session_of_goal(goal):
    return goal.split(".")[0]


# "Session.Theory"
def theory_of_goal(goal):
    return ".".join(goal.split(".")[1:])


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
            if self.kind != other.kind:
                return False
            # kinds are equal
            if self.kind == ResultKind.SUCCESS:
                return self.time_ms == other.time_ms
            return True
        raise NotImplementedError("Can only compare Result to itself.")

    def __lt__(self, other):
        if self.__class__ == other.__class__:
            if self.kind == ResultKind.SUCCESS and other.kind == ResultKind.SUCCESS:
                return self.time_ms < other.time_ms
            return self.kind < other.kind


def parse_file(mirabelle_log, timeout_ms, only_theory, only_session):
    lines = [
        squeezed for line in mirabelle_log.strip().split("\n") if is_replay_line(squeezed := squeeze(line))
    ]
    # print("\n".join(lines[:20]))

    excluded_not_from_theory_or_session = 0

    calls = []
    for line in lines:
        # See "Terminology" above.
        goal = " ".join(line.split(" ")[3:5])
        tail = " ".join(line.split(" ")[7:])
        command = "(".join(tail.split("(")[:-1]).strip()
        if command.startswith("("):
            if not command.endswith(")"):
                raise RuntimeError("Command " + repr(command) + " starts with '(' but doesn't end with ')'")
            command = command[1:-1]
        if "slam" in command and "metis" in command:
            raise RuntimeError("Line has both slam and metis:\n" + line)
        if "slam" in command:
            assert command.startswith("slam")
            method = "slam"
            facts = command[5:]
        elif "metis" in command:
            assert command.startswith("metis")
            method = "metis"
            options_and_facts = command[6:]
            if options_and_facts.startswith("("):
                facts = options_and_facts[options_and_facts.index(")")+2:]
            else:
                facts = options_and_facts
        elif "MIRABELLE SLEDGEHAMMER REPLAY TIMEOUT AFTER" in line:
            print(line)
            continue
        else:
            raise RuntimeError("Line is neither slam nor metis invocation nor mirabelle timeout:\n" + line)
        result = Result("(" + (tail.split("(")[-1]), timeout_ms)
        if only_theory and theory_of_goal(goal) != only_theory:
            excluded_not_from_theory_or_session += 1
            pass
        if only_session and session_of_goal(goal) != only_session:
            excluded_not_from_theory_or_session += 1
            pass
        else:
            calls.append({"goal": goal, "method": method, "command": command, "facts": facts, "result": result, "dubious_goal": None})

    print("EXCLUDED", excluded_not_from_theory_or_session, "GOALS NOT FROM SPECIFIED THEORY OR SESSION")
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

    # We make sure that for every invocation of metis with the extensionality
    # axiom, there is also an invocation without the extensionality axiom but
    # the same facts and arguments otherwise.
    # Otherwise we mark the "best call" we're returning as stemming from a
    # "dubious" goal to optionally exclude it from analysis later.
    # In reality, this is probably all down to the fact that SH minimizes
    # successful metis calls and completely harmless. But better safe than
    # sorry.
    def is_dubious_set_of_calls(metis_calls):
        for metis_call in metis_calls:
            is_call_with_ext = (
                metis_call["facts"] == "ext" or
                metis_call["facts"].startswith("ext ")
            )
            if is_call_with_ext:
                metis_command = metis_call["command"]
                assert metis_command.startswith("metis (")
                assert metis_command.endswith(metis_call["facts"])
                # "metis (..., ...)"
                metis_command_without_facts = metis_command[:-len(metis_call["facts"])].strip()
                def is_same_call_without_ext(other_metis_call):
                    other_metis_command = other_metis_call["command"]
                    # print(repr(other_metis_command))
                    # print(repr(" ".join(["ext", other_metis_call["facts"]])), "vs.", repr(metis_call["facts"]))
                    if metis_call["facts"] == "ext":
                        metis_call_facts_without_ext = ""
                    elif metis_call["facts"].startswith("ext "):
                        metis_call_facts_without_ext = metis_call["facts"][4:]
                    else:
                        raise RuntimeError("we checked these conditions earlier...")
                    return (
                        other_metis_command.startswith(metis_command_without_facts) and # the same arguments
                        not other_metis_call["facts"].startswith("ext") and # no ext
                        other_metis_call["facts"] == metis_call_facts_without_ext # but the same facts otherwise
                    )
                # Now there must be a call with the same prefix but without ext
                if not any(
                    [is_same_call_without_ext(other_metis_call) for other_metis_call in metis_calls]
                ):
                    # print("bad list of metis calls:")
                    print("bad call:", repr(metis_call["command"]))
                    # for other_metis_call in metis_calls:
                    #     print(repr(other_metis_call["command"]))
                    # raise RuntimeError("Bad list of metis calls")
                    return True
                return False

    # for goal, metis_calls in metis_calls_by_goal.items():
    #     if is_dubious_set_of_calls(metis_calls):
    #         print("FOUND DUBIOUS SET OF CALLS (see right above)")

    best_metis_by_goal = {}
    for goal, metis_calls in metis_calls_by_goal.items():
        if goal in best_metis_by_goal:
            raise RuntimeError("goal was processed twice")

        best_metis_call = best(metis_calls)

        previously_dubious = best_metis_call["dubious_goal"] # for sanity check

        if is_dubious_set_of_calls(metis_calls):
            assert (previously_dubious is None) or previously_dubious
            best_metis_call["dubious_goal"] = True
        else:
            assert (previously_dubious is None) or not previously_dubious
            best_metis_call["dubious_goal"] = False

        assert best_metis_call["dubious_goal"] is not None

        best_metis_by_goal[goal] = best_metis_call

    return best_metis_by_goal


def get_best_metis(calls):
    return list(get_best_metis_by_goal(calls).values())


def get_call_by_goal(calls, goal):
    for call in calls:
        if call["goal"] == goal:
            return call
    raise ValueError(f"No call with {goal} in calls.")


def goals_with_differing_facts(all_goals, slam_calls, metis_calls):
    differing_facts_goal_list = []
    differing_facts_slam_better_goal_list = []
    differing_facts_slam_better_and_metis_dubious_goal_list = []
    for goal in all_goals:
        slam_call = get_call_by_goal(slam_calls, goal)
        metis_call = get_call_by_goal(metis_calls, goal)
        if slam_call["facts"] != metis_call["facts"]: # and (not metis_call["facts"].startswith("ext") or slam_call["facts"] != metis_call["facts"][4:]):
            differing_facts_goal_list.append(goal)
            if slam_call["result"] < metis_call["result"]:
                differing_facts_slam_better_goal_list.append(goal)
                # print("DIFFERING FACTS, SLAM BETTER: " + goal)
                # print("SLAM COMMAND: ", slam_call["command"], slam_call["result"].as_string)
                # print("METIS COMMAND:", metis_call["command"], metis_call["result"].as_string)
                # print("SLAM FACTS:  ", repr(slam_call["facts"]))
                # print("METIS FACTS: ", repr(metis_call["facts"]))
                assert metis_call["dubious_goal"] is not None
                if metis_call["dubious_goal"]:
                    differing_facts_slam_better_and_metis_dubious_goal_list.append(goal)
    differing_facts_goals = set(differing_facts_goal_list)
    differing_facts_slam_better_goals = set(differing_facts_slam_better_goal_list)
    differing_facts_slam_better_and_metis_dubious_goals = set(differing_facts_slam_better_and_metis_dubious_goal_list)
    return differing_facts_goals, differing_facts_slam_better_goals, differing_facts_slam_better_and_metis_dubious_goals


def summarize(calls, label, plot_cactus, plot_cactus_scaled_metis, plot_scatter, plot_hist, invocation, exclude_differing_facts):
    all_goals = set(call["goal"] for call in calls)

    slam_calls = [call for call in calls if call["method"] == "slam"]
    metis_calls = get_best_metis(calls)

    differing_facts_goals, differing_facts_slam_better_goals, differing_facts_slam_better_and_metis_dubious_goals = goals_with_differing_facts(all_goals, slam_calls, metis_calls)
    print("TOTAL GOALS WITH DIFFERING FACTS:", len(differing_facts_goals))
    print("TOTAL GOALS WITH DIFFERING FACTS WHERE SLAM IS BETTER:", len(differing_facts_slam_better_goals))
    print("TOTAL GOALS WITH DIFFERING FACTS WHERE SLAM IS BETTER AND METIS DUBIOUS:", len(differing_facts_slam_better_and_metis_dubious_goals))

    if exclude_differing_facts == "all":
        print("EXCLUDING GOALS WITH DIFFERING FACTS")
        excluded_goals = differing_facts_goals
    elif exclude_differing_facts == "slam_better":
        print("EXCLUDING GOALS WITH DIFFERING FACTS WHERE SLAM IS BETTER")
        excluded_goals = differing_facts_slam_better_goals
    elif exclude_differing_facts == "slam_better_and_metis_dubious":
        print("EXCLUDING GOALS WITH DIFFERING FACTS WHERE SLAM IS BETTER AND METIS DUBIOUS")
        excluded_goals = differing_facts_slam_better_and_metis_dubious_goals
    elif exclude_differing_facts is None:
        print("LEAVING GOALS WITH DIFFERING FACTS")
        excluded_goals = set()
    else:
        raise ValueError(f"invalid value {exclude_differing_facts=}")

    # filter ground truth
    calls = [call for call in calls if call["goal"] not in excluded_goals]

    # reinitialize
    all_goals = set(call["goal"] for call in calls)
    slam_calls = [call for call in calls if call["method"] == "slam"]
    metis_calls = get_best_metis(calls)

    # sanity check
    differing_facts_goals, differing_facts_slam_better_goals, differing_facts_slam_better_and_metis_dubious_goals = goals_with_differing_facts(all_goals, slam_calls, metis_calls)
    print("TOTAL GOALS WITH DIFFERING FACTS:", len(differing_facts_goals))
    print("TOTAL GOALS WITH DIFFERING FACTS WHERE SLAM IS BETTER:", len(differing_facts_slam_better_goals))
    print("TOTAL GOALS WITH DIFFERING FACTS WHERE SLAM IS BETTER AND METIS DUBIOUS:", len(differing_facts_slam_better_and_metis_dubious_goals))

    failed = [call for call in calls if call["result"].is_failed()]
    timed_out = [call for call in calls if call["result"].is_timeout()]
    success = [call for call in calls if call["result"].is_success()]

    success_goals = set(call["goal"] for call in success)
    always_failed_or_timed_out_goals = all_goals - success_goals

    # print(f"{len(failed)} calls failed")
    # print(f"{len(timed_out)} calls timed out")
    # print(f"{len(success)} calls succeeded")

    print(f"{len(all_goals)} goals in total")
    print(f"{len(always_failed_or_timed_out_goals)} goals failed or timed out (all calls)")
    print(f"{len(success_goals)} goals succeeded")

    slam_fails = [call["goal"] for call in slam_calls if call["result"].is_failed()]
    slam_timeouts = [call["goal"] for call in slam_calls if call["result"].is_timeout()]
    slam_success = [call["goal"] for call in slam_calls if call["result"].is_success()]

    slam_fails_or_timeouts = slam_fails + slam_timeouts

    # print(slam_success[0])
    # print(slam_fails)

    # From now on "metis" means the best-performing metis variant for any particular goal.
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
                get_call_by_goal(slam_calls, goal)["result"].as_string.ljust(12) + goal
                for goal in sorted(slam_success_metis_fail_or_timeout) # , key=lambda goal: get_call_by_goal(slam_calls, goal)["result"])
            ]
        )
    )

    # print(slam_success_metis_fail_or_timeout)
    # print(sorted(list(slam_success_metis_fail_or_timeout))[:10])

    metis_success_slam_fail_or_timeout = set(metis_success) - set(slam_success)

    metis_success_slam_fail = set(metis_success) - set(slam_success) - set(slam_timeouts)
    print(f"metis success, slam fail: {str(len(metis_success_slam_fail))}")
    metis_success_slam_timeout = set(metis_success) - set(slam_success) - set(slam_fails)
    print(f"metis success, slam timeout: {str(len(metis_success_slam_timeout))}")

    print("10 easiest (to metis) problems where slam fails:")
    easiest_slam_fails = sorted(
        list(metis_success_slam_fail),
        key=lambda goal: get_call_by_goal(metis_calls, goal)["result"],
    )[:10]
    print("- " + "\n- ".join(easiest_slam_fails))

    print("10 easiest (to metis) problems where slam times out:")
    easiest_slam_timeouts = sorted(
        list(metis_success_slam_timeout),
        key=lambda goal: get_call_by_goal(metis_calls, goal)["result"],
    )[:10]
    print("- " + "\n- ".join(easiest_slam_timeouts))

    if plot_cactus:
        plot_success_calls(metis_calls, slam_calls, label, invocation)
    if plot_cactus_scaled_metis:
        plot_success_calls(metis_calls, slam_calls, label, invocation, scale_metis=True)

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
    print("BOTH SUCCESS, METIS FASTER:", metis_better)
    print("BOTH SUCCESS, SLAM FASTER:", slam_better)

    if plot_scatter:
        plt.rc("axes", axisbelow=True)
        plt.grid(True, which="major", color="0.5")

        # cm = plt.get_cmap('nipy_spectral')
        # color = cm(((135 * (invocation + 1)) % 360) / 360.)

        # plt.scatter(metis_both_success_times, [extrapolate(time) for time in metis_both_success_times], marker='.')
        # plt.scatter(metis_success_slam_fail_or_timeout_times, slam_fake_long_times, marker='x')
        # plt.scatter(metis_success_slam_fail_or_timeout_times, slam_fake_random_times, marker='x')
        
        min_time_minus = .4
        max_time_plus = max_time / .4

        # plt.hexbin(metis_both_success_times, slam_both_success_times, xscale="log", yscale="log", gridsize=140, lw=0.1, cmap="gnuplot2_r", extent=(np.log(min_time_minus), np.log(max_time_plus), np.log(min_time_minus), np.log(max_time_plus))) # , c=color, alpha=0.5) # , label=label)

        plt.scatter(metis_both_success_times, slam_both_success_times, marker=".", s=14, lw=0, alpha=0.5) # , c=color, alpha=0.5) # , label=label)

        plt.plot([min_time_minus, max_time_plus], [min_time_minus, max_time_plus], color="red", alpha=0.5) # , label="diagonal")

        # for n in range(10):
        #     xtimes = np.linspace(min_time_minus, max_time_plus)
        #     ytimes = xtimes * 10**n
        #     plt.plot(xtimes, ytimes, color="orange", alpha=0.5) # , label="diagonal")

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


def plot_success_calls(metis_calls, slam_calls, label, invocation, scale_metis=False):
    cm = plt.get_cmap('nipy_spectral')
    color = cm(((135 * invocation) % 360) / 360.)

    if scale_metis:
        label = "FAKE " + label

    metis_success = sorted(
        [call for call in metis_calls if call["result"].is_success()], key=lambda call: call["result"]
    )
    metis_successes = len(metis_success)
    metis_success_times = [call["result"].time_ms for call in metis_success]

    if scale_metis:
        metis_cumulative_problems = [i * 1000. / metis_successes for i, _ in enumerate(metis_success)]
    else:
        metis_cumulative_problems = [i for i, _ in enumerate(metis_success)]

    plt.plot(metis_success_times, metis_cumulative_problems, "+", color=color, label=label + " (metis)")

    slam_success = sorted(
        [call for call in slam_calls if call["result"].is_success()], key=lambda call: call["result"]
    )
    slam_successes = len(slam_success)
    slam_success_times = [call["result"].time_ms for call in slam_success]

    if scale_metis:
        slam_cumulative_problems = [i * 1000. / metis_successes for i, _ in enumerate(slam_success)]
    else:
        slam_cumulative_problems = [i for i, _ in enumerate(slam_success)]

    plt.plot(slam_success_times, slam_cumulative_problems, "+", color=color, label=label + " (slam)")


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
    parser.add_argument("-pcsm", "--plot-cactus-scaled-metis", action="store_true", help="create FAKE cactus plot scaled to have all metis runs equal")
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
    parser.add_argument(
        "-edf",
        "--exclude-differing-facts",
        type=str,
        required=True,
        help="Exclude calls where metis and slam were invoked with different sets of lemmas. Possible values: none, all, slam_better, slam_better_and_metis_dubious."
    )
    parser.add_argument(
        "-th",
        "--theory",
        type=str,
        help="Only include goals from the given theory."
    )
    parser.add_argument(
        "-se",
        "--session",
        type=str,
        help="Only include goals from the given session."
    )
    args = parser.parse_args()

    if args.theory and args.session:
        raise RuntimeError("specify at most on of --theory and --session")

    if sum(bool(arg) for arg in (args.plot_cactus, args.plot_cactus_scaled_metis, args.plot_scatter, args.plot_hist)) > 1:
        raise RuntimeError("specify at most one of --plot-cactus, --plot-cactus-scaled-metis, --plot-scatter and --plot-hist")

    plot_any = args.plot_cactus or args.plot_cactus_scaled_metis or args.plot_scatter or args.plot_hist
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
        try:
            with open(dirname + "/commit") as c:
                commit = c.read()[:7]
        except FileNotFoundError as e:
            commit = "UNKOWN_COMMIT"
        print(dirname, commit)

        filepath = dirname + "/mirabelle.log"
        if os.path.isfile(filepath):
            with open(filepath) as f:
                mirabelle_log = f.read()
        else:
            mirabelle_output_dir = dirname + "/mirabelle_output"
            session_log_dirs = [name for name in os.listdir(mirabelle_output_dir) if os.path.isdir(mirabelle_output_dir + "/" + name)]
            mirabelle_log = ""
            for session_log_dir in session_log_dirs:
                filepath = dirname + "/mirabelle_output/" + session_log_dir + "/mirabelle.log"
                with open(filepath) as f:
                    mirabelle_log += f.read()

        calls = parse_file(mirabelle_log, args.timeout_ms, args.theory, args.session)

        label = dirname + " " + commit
        summarize(
            calls, label, args.plot_cactus, args.plot_cactus_scaled_metis, args.plot_scatter, args.plot_hist, i, args.exclude_differing_facts
        )
        print()

    if args.theory:
        title_prefix = f"Theory {args.theory}: "
    elif args.session:
        title_prefix = f"Session {args.session}: "
    else:
        title_prefix = ""

    if args.plot_cactus:
        plt.xlabel("time [ms]")
        plt.ylabel("number of goals solved")
        plt.legend()
        plt.title(title_prefix + "metis vs. slam")

    if args.plot_cactus_scaled_metis:
        plt.xlabel("time [ms]")
        plt.ylabel("number of goals solved")
        plt.legend()
        plt.title(title_prefix + "FAKE! RUNS HAVE BEEN SCALED SO THAT METIS RUNS HAVE THE SAME HEIGHT!")

    if args.plot_scatter:
        plt.xscale("log")
        plt.yscale("log")

        plt.xlabel("metis time [ms]")
        plt.ylabel("slam time [ms]")
        # plt.legend()
        # plt.title(title_prefix + "metis vs. slam times")

    if args.plot_hist:
        plt.xscale("log")
        plt.xlabel("time [ms]")
        plt.ylabel("count")
        plt.legend()
        plt.title(title_prefix + "histograms")

    if plot_any:
        if args.save_plot:
            plt.savefig("plot.pdf")
        else:
            plt.show()
