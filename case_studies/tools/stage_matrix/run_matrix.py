#!/usr/bin/env python3
"""Run the stage-matrix binary over sets of .lrl files and collect JSON lines.

Usage (normally through ../run_stage_matrix.sh):
    run_matrix.py --bin <stage_matrix binary> --root <repo root> --out <results dir>
                  [--backend dynamic] [--jobs 4] [--timeout 600] SET=DIR [SET=DIR ...]

For every set, every `*.lrl` file below DIR (macOS `._*` files and `packages/` fixtures
excluded, sorted by path) is run as `<bin> --backend <b> <file>` with the repository root as
working directory. Output: <out>/<backend>/<set>.jsonl (the tool's records, each extended with
"set"), plus a `crash` record for a file whose run exits non-zero or ends without an `end` record.
"""
import argparse
import concurrent.futures
import json
import os
import subprocess
import sys


def list_files(root, rel_dir):
    base = os.path.join(root, rel_dir)
    out = []
    for dirpath, dirnames, filenames in os.walk(base):
        dirnames[:] = sorted(d for d in dirnames if not d.startswith(".") and d != "packages")
        for name in filenames:
            if name.startswith("._") or name.startswith(".") or not name.endswith(".lrl"):
                continue
            out.append(os.path.relpath(os.path.join(dirpath, name), root))
    return sorted(out)


def run_one(binary, root, backend, rel, timeout):
    cmd = [binary, "--backend", backend, rel]
    try:
        proc = subprocess.run(cmd, cwd=root, capture_output=True, text=True, timeout=timeout)
        stdout, stderr, code = proc.stdout, proc.stderr, proc.returncode
    except subprocess.TimeoutExpired as e:
        stdout = e.stdout.decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
        stderr = "timeout after %ss" % timeout
        code = "timeout"
    records = []
    for line in stdout.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            records.append(json.loads(line))
        except json.JSONDecodeError:
            pass
    has_end = any(r.get("record") == "end" for r in records)
    early_file_status = any(
        r.get("record") == "file" and r.get("status") != "ok" for r in records
    )
    if code != 0 or not (has_end or early_file_status):
        records.append({
            "record": "crash",
            "file": rel,
            "backend": backend,
            "exit": code,
            "stderr_tail": stderr[-600:],
        })
    return rel, records


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bin", required=True)
    ap.add_argument("--root", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--backend", default="dynamic")
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("sets", nargs="+")
    args = ap.parse_args()

    out_dir = os.path.join(args.out, args.backend)
    os.makedirs(out_dir, exist_ok=True)
    for spec in args.sets:
        name, rel_dir = spec.split("=", 1)
        if not os.path.isdir(os.path.join(args.root, rel_dir)):
            print("[stage-matrix] set %s: %s does not exist, skipped" % (name, rel_dir))
            target = os.path.join(out_dir, name + ".jsonl")
            if os.path.exists(target):
                os.remove(target)
            continue
        files = list_files(args.root, rel_dir)
        results = {}
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
            futures = [
                pool.submit(run_one, args.bin, args.root, args.backend, f, args.timeout)
                for f in files
            ]
            for fut in concurrent.futures.as_completed(futures):
                rel, records = fut.result()
                results[rel] = records
        with open(os.path.join(out_dir, name + ".jsonl"), "w") as fh:
            for rel in files:
                for rec in results[rel]:
                    rec["set"] = name
                    fh.write(json.dumps(rec, sort_keys=False) + "\n")
        crashes = sum(1 for rel in files for r in results[rel] if r.get("record") == "crash")
        print("[stage-matrix] %s/%s: %d files, %d crash records" % (args.backend, name, len(files), crashes))


if __name__ == "__main__":
    sys.exit(main())
