#!/usr/bin/env python3
"""Optional cross-check of the stage-matrix replay against the real CLI binary.

Usage: check_against_cli.py --cli <path to the lrl/cli binary> --results <results dir> --out <json>

For every file of the dynamic-prelude results, runs `<cli> run <file>` from the repository root
(the whole file at once, exactly as a user would) and compares (a) the multiset of diagnostic
codes on its `Error:` lines (`nocode` for an error without a code) with the multiset of error codes
of the per-form replay recorded by stage_matrix, and (b) non-zero exit status with "the replay
reported an error". Writes a JSON summary with every differing file.
"""
import argparse
import collections
import concurrent.futures
import json
import os
import re
import subprocess

ANSI = re.compile(r"\x1b\[[0-9;]*m")
ERROR_LINE = re.compile(r"^Error: (\[([A-Z]\d{3,4})\])?")


def cli_codes(cli, root, rel, timeout):
    try:
        proc = subprocess.run([cli, "run", rel], cwd=root, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return rel, "timeout", []
    text = ANSI.sub("", proc.stdout + proc.stderr)
    codes = []
    for line in text.splitlines():
        m = ERROR_LINE.match(line)
        if m:
            codes.append(m.group(2) or "nocode")
    return rel, proc.returncode, codes


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cli", required=True)
    ap.add_argument("--results", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--timeout", type=int, default=600)
    args = ap.parse_args()
    root = os.getcwd()
    rows = collections.OrderedDict()
    ddir = os.path.join(args.results, "dynamic")
    for name in sorted(os.listdir(ddir)):
        if not name.endswith(".jsonl") or name.startswith("._"):
            continue
        for line in open(os.path.join(ddir, name)):
            rec = json.loads(line)
            rows.setdefault(rec["file"], []).append(rec)
    files = list(rows)
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        results = list(pool.map(lambda f: cli_codes(args.cli, root, f, args.timeout), files))
    diffs = []
    for rel, code, codes in results:
        replay = [e.get("code") or "nocode" for r in rows[rel] if "cli" in r for e in r["cli"]["errors"]]
        same_codes = sorted(codes) == sorted(replay)
        same_status = code != "timeout" and ((code != 0) == bool(replay))
        if not (same_codes and same_status):
            diffs.append({"file": rel, "exit": code, "cli_codes": sorted(codes), "replay_codes": sorted(replay)})
    summary = {"cli": args.cli, "files": len(files), "same": len(files) - len(diffs), "diffs": diffs}
    with open(args.out, "w") as fh:
        json.dump(summary, fh, indent=1)
    print("[stage-matrix] CLI cross-check: %d files, %d identical, %d differ" % (len(files), summary["same"], len(diffs)))


if __name__ == "__main__":
    main()
