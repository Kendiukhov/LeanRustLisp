#!/usr/bin/env python3
"""Summarise a macOS `sample` call graph (see bench/results/profiles.txt).

  python3 bench/sample_summary.py <sample report> <frame> [<frame> ...]

For each frame name (Rust symbol without its `::h<hash>` suffix), prints the number of samples in
its outermost occurrences (recursive occurrences nested inside another occurrence are not counted
again) and how they split over its direct callees. Lines of the report that `sample` truncated or
that do not match the call-graph format are ignored.
"""
import re, sys
from collections import defaultdict
path, *targets = sys.argv[1:]
lines = open(path).read().split("Call graph:")[1].split("Total number in stack")[0].splitlines()
pat = re.compile(r"^([ +!:|]*)(\d+) (.+?)(?:  \(in [^)]*\).*)?$")
nodes = []  # (depth, count, name)
for l in lines:
    m = pat.match(l)
    if not m:
        continue
    depth = len(m.group(1)); cnt = int(m.group(2))
    name = re.sub(r"::h[0-9a-f]{16}$", "", m.group(3).strip())
    nodes.append((depth, cnt, name))
total_lrl = 0
for t in targets:
    agg = defaultdict(int); tot = 0
    for i, (d, c, n) in enumerate(nodes):
        if n != t:
            continue
        # skip recursive occurrences nested under another occurrence of t
        nested = False
        for j in range(i - 1, -1, -1):
            if nodes[j][0] < d:
                d2 = nodes[j][0]
                if nodes[j][2] == t:
                    nested = True
                    break
                d = d2
        if nested:
            continue
        tot += c
        dd = nodes[i][0]
        child_depth = None
        for k in range(i + 1, len(nodes)):
            if nodes[k][0] <= dd:
                break
            if child_depth is None:
                child_depth = nodes[k][0]
            if nodes[k][0] == child_depth:
                agg[nodes[k][2]] += nodes[k][1]
    print(f"== {t}: {tot} samples (outermost occurrences)")
    for n, c in sorted(agg.items(), key=lambda kv: -kv[1])[:8]:
        print(f"   {c:6d}  {n}")
