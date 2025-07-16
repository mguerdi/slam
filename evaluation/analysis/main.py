from enum import Enum, auto
from functools import total_ordering
import os


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
    def __init__(self, as_string):
        self.as_string = as_string
        self.kind = ResultKind.from_string(as_string)
        if self.kind == ResultKind.SUCCESS:
            self.time_ms = parse_time_ms(as_string)

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


def parse_file(filename):
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
        if "jeha" in command and "metis" in command:
            raise RuntimeError("Line has both jeha and metis:\n" + line)
        if "jeha" in command:
            method = "jeha"
        elif "metis" in command:
            method = "metis"
        else:
            raise RuntimeError("Line has neither jeha nor metis:\n" + line)
        result = Result("(" + (tail.split("(")[-1]))
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


def summarize(calls):
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

    jeha_calls = [call for call in calls if call["method"] == "jeha"]

    jeha_fails = [call["goal"] for call in jeha_calls if call["result"].is_failed()]
    jeha_timeouts = [call["goal"] for call in jeha_calls if call["result"].is_timeout()]
    jeha_success = [call["goal"] for call in jeha_calls if call["result"].is_success()]

    jeha_fails_or_timeouts = jeha_fails + jeha_timeouts

    # print(jeha_success[0])
    # print(jeha_fails)

    # From now on "metis" means the best-performing metis variant for any particular goal.
    metis_calls = get_best_metis(calls)

    metis_fails = [call["goal"] for call in metis_calls if call["result"].is_failed()]
    metis_timeouts = [call["goal"] for call in metis_calls if call["result"].is_timeout()]
    metis_success = [call["goal"] for call in metis_calls if call["result"].is_success()]

    metis_fails_or_timeouts = metis_fails + metis_timeouts

    # print(metis_any_success[0])
    print(f"jeha fails: {len(jeha_fails)}")
    print(f"jeha timeouts: {len(jeha_timeouts)}")
    print(f"jeha success: {len(jeha_success)}")
    print(f"metis fails (no variant worked): {len(metis_fails)}")
    print(f"metis timeouts (no variant worked): {len(metis_timeouts)}")
    print(f"metis success (any variant worked): {len(metis_success)}")

    jeha_success_metis_fail_or_timeout = set(jeha_success) - set(metis_success)

    print(f"jeha success, metis fail or timeout: {str(len(jeha_success_metis_fail_or_timeout))}")
    print(jeha_success_metis_fail_or_timeout)
    # print(sorted(list(jeha_success_metis_fail_or_timeout))[:10])
    print(
        f"metis success, jeha fail or timeout: {str(len(set(jeha_fails_or_timeouts) - set(metis_fails_or_timeouts)))}"
    )


if __name__ == "__main__":
    if not os.path.isdir("runs"):
        raise RuntimeError("Couldn't find directory with name 'runs'.")
    runs_dirs = sorted(list(os.listdir("runs")))
    for dirname in runs_dirs:
        filename = "runs/" + dirname + "/mirabelle.log"
        with open("runs/" + dirname + "/commit") as c:
            commit = c.read()
        print(filename, commit)
        try:
            calls = parse_file(filename)
            summarize(calls)
        except FileNotFoundError:
            print(f"skipping {filename} (not found)")
        print()
