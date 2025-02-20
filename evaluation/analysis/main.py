import os

# Instructions:
# # create directory for this run
# mkdir ~/analysis/runs/run1
# # in jeha
# git rev-parse HEAD > ~/analysis/runs/run1/commit
# # in home
# ./replay_mirabelle_sledgehammer.sh
# # copy to run
# cp ~/mirabelle_output/mirabelle.log analysis/runs/run1/
# # view results
# python3 main.py

def squeeze(line):
    # tr -s ' '
    return " ".join(part for part in line.split(" ") if len(part) > 0)

def is_replay_line(line):
    mirabelle_command = line.split(" ")[0]
    mirabelle_kind = line.split(" ")[1]
    return "error: No mini preplay input for" not in line and mirabelle_command == "0.sledgehammer_replay" and mirabelle_kind not in ["finalize", "initialize"]

def analyse_file(filename):
    with open(filename) as f:
        s = f.read()
    lines = [squeezed for line in s.strip().split("\n") if is_replay_line(squeezed:=squeeze(line))]
    # print("\n".join(lines[:20]))
    results = []
    for line in lines:
        path = " ".join(line.split(" ")[3:5])
        tail = " ".join(line.split(" ")[7:])
        call = "(".join(tail.split("(")[:-1])
        if "jeha" in call and "metis" in call:
            raise RuntimeError("Line has both jeha and metis:\n" + line)
        if "jeha" in call:
            method = "jeha"
        elif "metis" in call:
            method = "metis"
        else:
            raise RuntimeError("Line has neither jeha nor metis:\n" + line)
        result = "(" + (tail.split("(")[-1])
        results.append({"path": path, "method": method, "call": call, "result": result})
    
    def is_failed(goal):
        return "failed" in goal["result"]
    
    def is_timeout(goal):
        return "timed out" in goal["result"]
    
    def is_success(goal):
        return not is_failed(goal) and not is_timeout(goal)
    
    failed = [goal for goal in results if is_failed(goal)]
    timed_out = [goal for goal in results if is_timeout(goal)]
    success = [goal for goal in results if is_success(goal)]
    print(f"{len(failed)} failed")
    print(f"{len(timed_out)} timed out")
    print(f"{len(success)} succeeded")
    jeha_fails_or_timeouts = [goal["path"] for goal in failed + timed_out if goal["method"] == "jeha"]
    # print(jeha_fails)
    metis_grouped = {}
    for goal in results:
        if goal["method"] == "metis":
            path = goal["path"]
            if path in metis_grouped:
                metis_grouped[path].append(goal)
            else:
                metis_grouped[path] = [goal]
    metis_all_fails_or_timeouts = [path for path, goals in metis_grouped.items() if all(not is_success(goal) for goal in goals)]
    print(f"jeha fails or timeouts: {len(jeha_fails_or_timeouts)}")
    print(f"metis fails (no variant worked): {len(metis_all_fails_or_timeouts)}")
    jeha_success_metis_fail_or_timeout = set(metis_all_fails_or_timeouts) - set(jeha_fails_or_timeouts)
    print(f"jeha success, metis fail: {str(len(jeha_success_metis_fail_or_timeout))}")
    print(jeha_success_metis_fail_or_timeout)
    print(f"metis success, jeha fail: {str(len(set(jeha_fails_or_timeouts) - set(metis_all_fails_or_timeouts)))}")
    
if __name__ == "__main__":
    if not os.path.isdir("runs"):
        raise RuntimeError("Couldn't find directory with name 'runs'.")
    runs_dirs = os.listdir("runs")
    for dirname in runs_dirs:
        filename = "runs/" + dirname + "/mirabelle.log"
        print(filename)
        try:
            analyse_file(filename)
        except FileNotFoundError:
            print(f"skipping {filename} (not found)")
        print()
