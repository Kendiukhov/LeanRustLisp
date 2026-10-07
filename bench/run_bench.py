#!/usr/bin/env python3
"""LRL benchmark driver.

Measures, with wall-clock time (time.perf_counter around subprocess.run):
  compile   compile time of the case studies (CLI total, CLI front half, rustc alone)
  runtime   run time of workloads derived from the case studies, for several sizes n
  proof     residual cost of an Eq proof argument (A/B pair, interleaved runs)
  rustref   a plain-Rust reference for the vector workload (context only)
and writes raw CSV files to bench/results/ plus bench/results/summary.md (`summary`).

Run from anywhere; the LRL CLI is always run with cwd = repository root (it finds stdlib/ relative
to the current directory). See bench/README.md for the methodology.

  python3 bench/run_bench.py check                          # copied case-study forms unchanged?
  python3 bench/run_bench.py all --lrl <path to release cli>
  python3 bench/run_bench.py summary
"""

import argparse
import csv
import datetime
import math
import os
import re
import shutil
import statistics
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
BENCH = REPO / "bench"
PROGRAMS = BENCH / "programs"
RESULTS = BENCH / "results"
ANSI = re.compile(r"\x1b\[[0-9;]*m")

# ------------------------------------------------------------------------------------------------
# Experiment configuration
# ------------------------------------------------------------------------------------------------

CASE_STUDIES = ["case_studies/lrl/vectors.lrl", "case_studies/lrl/protocol.lrl"]
BACKENDS = ["typed", "dynamic"]
# "cli": the binary produced by `lrl compile` (rustc without optimisation flags, as the CLI calls it)
# "O":   the same generated Rust rebuilt with `rustc -O <file>.rs -o <bin>`
FLAGS = ["cli", "O"]

# Sizes n = A*B; the program computes n at run time as (nat_mul A B). n doubles from size to size.
# The largest size of vec_build_sum, list_fold and proto_send is one step beyond the largest n at
# which the typed backend's CLI binary still ran with a 64 MiB stack in exploratory runs, so that
# the stack limit is recorded by the driver itself (status "stack overflow").
WORKLOAD_SIZES = {
    "size_only": [(100, 1), (1000, 1), (100, 16), (1000, 32), (1000, 256)],
    "vec_build_sum": [(1000, k) for k in (1, 2, 4, 8, 16, 32, 64, 128)],
    "list_fold": [(1000, k) for k in (1, 2, 4, 8, 16, 32, 64, 128, 256)],
    "proto_send": [(1000, k) for k in (1, 2, 4, 8, 16, 32, 64)],
    "vec_rev_sum": [(100, k) for k in (1, 2, 4, 8, 16)],
}
WORKLOADS = list(WORKLOAD_SIZES)

PROOF_SIZES = [(1000, 1000), (2000, 2000)]  # A*B calls of `step`

RUST_REF_SIZES = [100, 200, 400, 800, 1600]

# Compile-time probe: front half of `lrl compile` for a closed size expression in a type index
# (vec_build_sum_closed_index.lrl) vs the same size passed to a function (vec_build_sum.lrl).
INDEXCOST_SIZES = [(250, 1), (500, 1), (1000, 1)]

# Generated programs recurse once per element; the measured binaries need a large stack.
REQUIRED_STACK_BYTES = 64 * 1024 * 1024 - 1024 * 1024  # `ulimit -s 65520` (KiB) satisfies this

# Repetitions: >= 10 for runs under 10 s, 5 above (decided from the first warm-up run); 20 for
# runs under 0.5 s, where process start-up noise is relatively larger.
REPS_VERY_FAST = 20
VERY_FAST_THRESHOLD_S = 0.5
REPS_FAST = 10
REPS_SLOW = 5
SLOW_THRESHOLD_S = 10.0
WARMUP_FAST = 2  # warm-up runs when the first warm-up took < 1 s
WARMUP_SLOW = 1
# A configuration (workload, backend, flags) stops growing n once a size's median exceeds this.
SIZE_CAP_S = 10.0
# A single run longer than this is killed and recorded as a timeout.
RUN_TIMEOUT_S = 600.0

BUSY_PROCESS = re.compile(
    r"(^|/)(cargo|rustc|lean|lake|leanc|idris2|racket|raco|ghc|cli|lrl[^/ ]*)$"
)

# ------------------------------------------------------------------------------------------------
# Helpers
# ------------------------------------------------------------------------------------------------


def now_iso():
    return datetime.datetime.now().isoformat(timespec="seconds")


def loadavg():
    try:
        return os.getloadavg()
    except OSError:
        return (float("nan"),) * 3


def timed(cmd, cwd=REPO, env=None, timeout=RUN_TIMEOUT_S):
    """Run cmd; return (seconds, returncode, stdout, stderr). Output is captured (piped)."""
    start = time.perf_counter()
    try:
        proc = subprocess.run(
            cmd, cwd=str(cwd), env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        elapsed = time.perf_counter() - start
        out = exc.stdout.decode("utf-8", "replace") if exc.stdout else ""
        err = exc.stderr.decode("utf-8", "replace") if exc.stderr else ""
        return elapsed, "timeout", out, err
    elapsed = time.perf_counter() - start
    return (
        elapsed,
        proc.returncode,
        proc.stdout.decode("utf-8", "replace"),
        proc.stderr.decode("utf-8", "replace"),
    )


def busy_processes():
    """Processes that would disturb a measurement (compilers, provers, other LRL CLIs)."""
    out = subprocess.run(["ps", "-A", "-o", "pid=,pcpu=,comm="], stdout=subprocess.PIPE,
                         text=True).stdout
    me = os.getpid()
    found = []
    for line in out.splitlines():
        parts = line.strip().split(None, 2)
        if len(parts) < 3:
            continue
        pid, pcpu, comm = parts
        if int(pid) == me:
            continue
        if BUSY_PROCESS.search(comm.strip()):
            found.append(f"{pid}:{os.path.basename(comm.strip())}:{pcpu}%")
    return found


def top_cpu_processes(limit=3, min_pcpu=10.0):
    out = subprocess.run(["ps", "-A", "-r", "-o", "pid=,pcpu=,comm="], stdout=subprocess.PIPE,
                         text=True).stdout
    me = os.getpid()
    top = []
    for line in out.splitlines():
        parts = line.strip().split(None, 2)
        if len(parts) < 3:
            continue
        pid, pcpu, comm = parts
        try:
            if int(pid) == me or float(pcpu) < min_pcpu:
                continue
        except ValueError:
            continue
        top.append(f"{pid}:{os.path.basename(comm.strip())}:{pcpu}%")
        if len(top) >= limit:
            break
    return top


class Recorder:
    """Appends raw rows to CSV files in bench/results and logs measurement batches."""

    def __init__(self, results_dir, wait_max):
        self.results_dir = Path(results_dir)
        self.results_dir.mkdir(parents=True, exist_ok=True)
        self.wait_max = wait_max
        self.batch = None

    def start_batch(self, name):
        waited = 0.0
        busy = busy_processes()
        while busy and waited < self.wait_max:
            print(f"  waiting: busy processes {busy}", flush=True)
            time.sleep(15)
            waited += 15
            busy = busy_processes()
        uptime = subprocess.run(["uptime"], stdout=subprocess.PIPE, text=True).stdout.strip()
        self.batch = f"{name}@{now_iso()}"
        row = {
            "batch": self.batch,
            "time": now_iso(),
            "uptime": uptime,
            "busy_processes": " ".join(busy) if busy else "none",
            "waited_s": f"{waited:.0f}",
            "top_cpu_processes": " ".join(top_cpu_processes()) or "none",
        }
        self.append("batches.csv", row)
        print(f"[batch] {self.batch} | {uptime} | busy: {row['busy_processes']} | "
              f"top: {row['top_cpu_processes']}", flush=True)

    def append(self, filename, row):
        path = self.results_dir / filename
        new = not path.exists()
        with open(path, "a", newline="") as fh:
            writer = csv.DictWriter(fh, fieldnames=list(row.keys()))
            if new:
                writer.writeheader()
            writer.writerow(row)


def instantiate(template, out_path, **subst):
    text = template.read_text()
    for key, value in subst.items():
        text = text.replace(f"@{key}@", value)
    if re.search(r"@[A-Z_]+@", text.split("\n;; ---- workload ----")[-1]):
        raise SystemExit(f"unsubstituted placeholder in {out_path}")
    out_path.write_text(text)
    return out_path


def cli_compile(lrl, src, backend, out_bin, env=None, keep_source_as=None, clean=True):
    """`lrl compile <src> --backend <backend> -o <out_bin>` from the repository root.

    Returns (seconds, returncode, generated_source_or_None, output_text). The generated Rust
    source (build/output_<tag>.rs) is copied to keep_source_as when given; with clean=True the
    source and the incremental-cache session directory of this compile are removed from build/.
    """
    cmd = [str(lrl), "compile", str(src), "--backend", backend, "-o", str(out_bin)]
    secs, rc, out, err = timed(cmd, env=env)
    text = ANSI.sub("", out + err)
    sources = re.findall(r"Compiling (build/output_[0-9_]+(?:_dynamic)?\.rs) to", text)
    ok = (rc == 0 and "Compilation successful" in text and "falling back" not in text
          and len(sources) == 1)
    generated = REPO / sources[0] if sources else None
    if generated is not None and generated.exists():
        if keep_source_as is not None:
            shutil.copyfile(generated, keep_source_as)
        if clean:
            tag = re.match(r"output_([0-9]+_[0-9]+)", generated.name).group(1)
            generated.unlink()
            incr = REPO / "build" / "incremental"
            for entry in incr.glob(f"output_{tag}-*"):
                shutil.rmtree(entry, ignore_errors=True)
    return secs, (rc if ok else f"fail:{rc}"), generated, text


def rustc_build(src, out_bin, mode, scratch):
    """Rebuild generated Rust. mode 'cli': exactly the CLI's flags with a fresh incremental dir;
    mode 'O': `rustc -O <src> -o <bin>`."""
    if mode == "cli":
        incr = Path(scratch) / f"incr_{os.getpid()}_{time.time_ns()}"
        incr.mkdir(parents=True)
        cmd = ["rustc", str(src), "-o", str(out_bin), "-C", f"incremental={incr}"]
        result = timed(cmd)
        shutil.rmtree(incr, ignore_errors=True)
    elif mode == "O":
        cmd = ["rustc", "-O", str(src), "-o", str(out_bin)]
        result = timed(cmd)
    else:
        raise ValueError(mode)
    return result


def failure_status(rc, out, err):
    if "overflowed its stack" in out + err:
        return f"error:{rc} (stack overflow)"
    if rc == 0:
        return "error: wrong or missing Result line"
    return f"error:{rc}"


def check_stack():
    import resource
    soft, _hard = resource.getrlimit(resource.RLIMIT_STACK)
    if soft != resource.RLIM_INFINITY and soft < REQUIRED_STACK_BYTES:
        raise SystemExit(
            f"stack soft limit is {soft // 1024} KiB; run `ulimit -s 65520` in the shell before "
            f"this driver (the generated programs recurse once per element)")
    return soft


def result_value(stdout):
    """Last `Result: N` / `Result: Nat(N)` line of a compiled LRL program."""
    m = re.findall(r"^Result: (?:Nat\()?([0-9]+)\)?\s*$", stdout, re.M)
    return int(m[-1]) if m else None


def make_shim(work):
    """A no-op `rustc` used to time the LRL front half: it creates the -o file and exits 0."""
    shim_dir = Path(work) / "shim"
    shim_dir.mkdir(parents=True, exist_ok=True)
    shim = shim_dir / "rustc"
    shim.write_text(
        "#!/bin/sh\n"
        "# no-op rustc (bench/run_bench.py): creates the -o file and exits 0\n"
        "out=\"\"\n"
        "while [ $# -gt 0 ]; do\n"
        "  if [ \"$1\" = \"-o\" ]; then shift; out=\"$1\"; fi\n"
        "  shift\n"
        "done\n"
        "[ -n \"$out\" ] && : > \"$out\"\n"
        "exit 0\n"
    )
    shim.chmod(0o755)
    env = dict(os.environ)
    env["PATH"] = f"{shim_dir}{os.pathsep}{env.get('PATH', '')}"
    return env


def measure(rec, csv_name, base_row, fn, check=None, reps=None, warmup=None):
    """Warm-up + repetitions of fn() -> (secs, rc, out, err). Appends one CSV row per run.
    Returns the list of measured (non-warm-up) seconds, or None when a run failed."""
    times = []
    first = None
    n_warm = warmup
    i = 0
    while True:
        is_warm = n_warm is None or i < n_warm
        secs, rc, out, err = fn()
        good = rc == 0 and (check is None or check(out))
        la = loadavg()
        row = dict(base_row)
        row.update({
            "batch": rec.batch, "time": now_iso(), "warmup": int(is_warm),
            "rep": i if is_warm else i - n_warm, "seconds": f"{secs:.6f}",
            "status": "ok" if good else failure_status(rc, out, err),
            "load1": f"{la[0]:.2f}", "load5": f"{la[1]:.2f}", "load15": f"{la[2]:.2f}",
        })
        rec.append(csv_name, row)
        if not good:
            print(f"    run failed: rc={rc} out={out[-300:]!r} err={err[-300:]!r}", flush=True)
            return None
        if n_warm is None:  # first warm-up decides the plan
            first = secs
            n_warm = WARMUP_FAST if secs < 1.0 else WARMUP_SLOW
            if reps is None:
                reps = (REPS_VERY_FAST if secs < VERY_FAST_THRESHOLD_S
                        else REPS_FAST if secs < SLOW_THRESHOLD_S else REPS_SLOW)
        if not is_warm:
            times.append(secs)
        i += 1
        if len(times) >= reps:
            break
    print(f"    {base_row} median={statistics.median(times):.4f}s min={min(times):.4f}s "
          f"max={max(times):.4f}s runs={len(times)} (first warm-up {first:.3f}s)", flush=True)
    return times


# ------------------------------------------------------------------------------------------------
# check: copied case-study forms
# ------------------------------------------------------------------------------------------------


def top_level_forms(text):
    """Top-level s-expressions of an LRL file (comments removed), as (head, name, normalised)."""
    forms, depth, cur, i = [], 0, [], 0
    in_str = False
    while i < len(text):
        c = text[i]
        if in_str:
            cur.append(c)
            if c == "\\":
                cur.append(text[i + 1])
                i += 1
            elif c == '"':
                in_str = False
        elif c == ";":
            while i < len(text) and text[i] != "\n":
                i += 1
            continue
        elif c == '"':
            in_str = True
            cur.append(c)
        elif c == "(":
            depth += 1
            cur.append(c)
        elif c == ")":
            depth -= 1
            cur.append(c)
            if depth == 0:
                forms.append("".join(cur))
                cur = []
        elif depth > 0:
            cur.append(c)
        i += 1
    result = []
    for f in forms:
        norm = " ".join(f.replace("(", " ( ").replace(")", " ) ").split())
        toks = norm.split()
        head = toks[1]
        if head == "inductive" and toks[2] == "(":  # marker list, e.g. (inductive (affine) Chan ...)
            j = toks.index(")", 2)
            name = toks[j + 1]
        else:
            name = toks[2]
        result.append((head, name, norm))
    return result


def cmd_check(_args):
    problems = 0
    for tpl in sorted(p for p in PROGRAMS.glob("*.lrl") if not p.name.startswith("._")):
        text = tpl.read_text()
        m = re.search(r"^;; @copied-from (\S+): (.+)$", text, re.M)
        if not m:
            print(f"{tpl.name}: no @copied-from line (self-contained)")
            continue
        source = REPO / m.group(1)
        names = m.group(2).split()
        src_forms = {name: norm for _h, name, norm in top_level_forms(source.read_text())}
        tpl_forms = {name: norm for _h, name, norm in top_level_forms(text)}
        for name in names:
            if name not in src_forms:
                print(f"{tpl.name}: {name}: MISSING in {m.group(1)}")
                problems += 1
            elif name not in tpl_forms:
                print(f"{tpl.name}: {name}: MISSING in template")
                problems += 1
            elif src_forms[name] != tpl_forms[name]:
                print(f"{tpl.name}: {name}: DIFFERS from {m.group(1)}")
                problems += 1
            else:
                print(f"{tpl.name}: {name}: identical to {m.group(1)}")
    print(f"check: {problems} problem(s)")
    return 1 if problems else 0


# ------------------------------------------------------------------------------------------------
# machine
# ------------------------------------------------------------------------------------------------


def sh(cmd):
    try:
        return subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                              cwd=str(REPO)).stdout.strip()
    except OSError as exc:
        return f"<{exc}>"


def cmd_machine(args):
    lines = [
        f"date: {now_iso()}",
        f"machdep.cpu.brand_string: {sh(['sysctl', '-n', 'machdep.cpu.brand_string'])}",
        f"hw.ncpu: {sh(['sysctl', '-n', 'hw.ncpu'])}",
        f"hw.perflevel0.physicalcpu (performance cores): "
        f"{sh(['sysctl', '-n', 'hw.perflevel0.physicalcpu'])}",
        f"hw.perflevel1.physicalcpu (efficiency cores): "
        f"{sh(['sysctl', '-n', 'hw.perflevel1.physicalcpu'])}",
        f"hw.memsize: {sh(['sysctl', '-n', 'hw.memsize'])}",
        "sw_vers:", sh(["sw_vers"]),
        "rustc -vV:", sh(["rustc", "-vV"]),
        f"cargo -V: {sh(['cargo', '-V'])}",
        f"python: {sys.version.split()[0]} ({sys.executable})",
        f"uptime: {sh(['uptime'])}",
        f"stack soft limit for measured processes (ulimit -s, KiB): "
        f"{__import__('resource').getrlimit(__import__('resource').RLIMIT_STACK)[0] // 1024}",
    ]
    if args.lrl:
        lrl = Path(args.lrl)
        lines.append(f"lrl binary: {lrl} ({lrl.stat().st_size} bytes)")
        lines.append(f"lrl sha256: {sh(['shasum', '-a', '256', str(lrl)]).split()[0]}")
    lines.append(f"git HEAD: {sh(['git', 'rev-parse', 'HEAD'])}")
    # Not counting results files (which reruns of the scripts rewrite) or the paper.
    status = [l for l in sh(["git", "status", "--short", "--", ".", ":!**/results_*.md", ":!**/SUMMARY.md",
                             ":!bench/results", ":!paper"]).splitlines()
              if not l.startswith("error:")]
    lines.append(f"git status --short (outside results files and paper/): {len(status)} entries "
                 f"({sum(1 for l in status if l.startswith(' M'))} modified, "
                 f"{sum(1 for l in status if l.startswith('??'))} untracked, "
                 f"{sum(1 for l in status if l.startswith(' D'))} deleted)")
    lines.append(f"git diff --shortstat (tracked files vs HEAD): "
                 f"{' '.join(l for l in sh(['git', 'diff', '--shortstat']).splitlines() if not l.startswith('error:'))}")
    text = "\n".join(lines) + "\n"
    RESULTS.mkdir(parents=True, exist_ok=True)
    (RESULTS / "machine.txt").write_text(text)
    print(text)
    return 0


# ------------------------------------------------------------------------------------------------
# compile: compile time of the case studies
# ------------------------------------------------------------------------------------------------


def cmd_compile(args):
    rec = Recorder(RESULTS, args.wait_max)
    work = Path(args.work_dir) / "compile"
    work.mkdir(parents=True, exist_ok=True)
    shim_env = make_shim(work)
    for cs in CASE_STUDIES:
        stem = Path(cs).stem
        for backend in BACKENDS:
            rec.start_batch(f"compile:{stem}:{backend}")
            base = {"program": cs, "backend": backend}
            out_bin = work / f"{stem}_{backend}.bin"
            gen_rs = work / f"{stem}_{backend}.rs"

            def total():
                secs, rc, _gen, text = cli_compile(args.lrl, cs, backend, out_bin,
                                                   keep_source_as=gen_rs)
                return secs, rc, text, ""

            def front():
                secs, rc, _gen, text = cli_compile(args.lrl, cs, backend, out_bin, env=shim_env)
                return secs, rc, text, ""

            measure(rec, "compile_time.csv", dict(base, phase="cli_total"), total)
            lines = sum(1 for _ in open(gen_rs))
            rec.append("generated_sources.csv", {
                "program": cs, "backend": backend, "file": str(gen_rs.relative_to(REPO))
                if gen_rs.is_relative_to(REPO) else str(gen_rs),
                "lines": lines, "bytes": gen_rs.stat().st_size, "time": now_iso()})
            measure(rec, "compile_time.csv", dict(base, phase="cli_front_noop_rustc"), front)
            for mode, phase in (("cli", "rustc_cli_flags"), ("O", "rustc_O")):
                bin_path = work / f"{stem}_{backend}_{mode}.bin"
                measure(rec, "compile_time.csv", dict(base, phase=phase),
                        lambda m=mode, b=bin_path: rustc_build(gen_rs, b, m, work))
    return 0


# ------------------------------------------------------------------------------------------------
# runtime: workloads x sizes x backends x flags
# ------------------------------------------------------------------------------------------------


def build_variants(args, rec, template, label, subst, work, backends=BACKENDS):
    """Instantiate a template and build it with the given backends (CLI binary + `rustc -O`
    rebuild of the generated Rust); returns {(backend, flags): binary}."""
    src = instantiate(PROGRAMS / template, work / f"{label}.lrl", **subst)
    bins = {}
    for backend in backends:
        gen_rs = work / f"{label}_{backend}.rs"
        bin_cli = work / f"{label}_{backend}_cli.bin"
        secs, rc, _gen, text = cli_compile(args.lrl, src, backend, bin_cli, keep_source_as=gen_rs)
        if rc != 0:
            print(f"  BUILD FAILED {label} {backend}: {text[-800:]}", flush=True)
            rec.append("builds.csv", {"label": label, "backend": backend, "flags": "cli",
                                      "status": f"error:{rc}", "build_seconds": f"{secs:.3f}",
                                      "binary_bytes": "", "time": now_iso()})
            continue
        rec.append("builds.csv", {"label": label, "backend": backend, "flags": "cli",
                                  "status": "ok", "build_seconds": f"{secs:.3f}",
                                  "binary_bytes": bin_cli.stat().st_size, "time": now_iso()})
        bins[(backend, "cli")] = bin_cli
        bin_o = work / f"{label}_{backend}_O.bin"
        secs, rc, _out, err = rustc_build(gen_rs, bin_o, "O", work)
        status = "ok" if rc == 0 else f"error:{rc}"
        rec.append("builds.csv", {"label": label, "backend": backend, "flags": "O",
                                  "status": status, "build_seconds": f"{secs:.3f}",
                                  "binary_bytes": bin_o.stat().st_size if rc == 0 else "",
                                  "time": now_iso()})
        if rc == 0:
            bins[(backend, "O")] = bin_o
        else:
            print(f"  rustc -O FAILED {label} {backend}: {err[-800:]}", flush=True)
    return bins


def cmd_runtime(args):
    rec = Recorder(RESULTS, args.wait_max)
    work = Path(args.work_dir) / "runtime"
    work.mkdir(parents=True, exist_ok=True)
    workloads = args.workloads.split(",") if args.workloads else WORKLOADS
    for wl in workloads:
        # (backend, flags) configurations that stopped growing n -> status recorded for the
        # larger sizes (a size's median exceeded SIZE_CAP_S, or a run at a size failed)
        stopped = {}
        for (a, b) in WORKLOAD_SIZES[wl]:
            n = a * b
            label = f"{wl}_n{n}"
            pending = [(be, fl) for be in BACKENDS for fl in FLAGS if (be, fl) not in stopped]
            if not pending:
                break
            bins = build_variants(args, rec, f"{wl}.lrl", label,
                                  {"SIZE": f"(nat_mul {a} {b})"}, work,
                                  backends=sorted({be for be, _fl in pending}))
            for backend in BACKENDS:
                for flags in FLAGS:
                    base = {"workload": wl, "n": n, "backend": backend, "flags": flags}
                    if (backend, flags) in stopped:
                        rec.append("runtime.csv", dict(base, batch="", time=now_iso(), warmup=0,
                                                       rep="", seconds="",
                                                       status=stopped[(backend, flags)],
                                                       load1="", load5="", load15=""))
                        continue
                    binary = bins.get((backend, flags))
                    if binary is None:
                        rec.append("runtime.csv", dict(base, batch="", time=now_iso(), warmup=0,
                                                       rep="", seconds="", status="build failed",
                                                       load1="", load5="", load15=""))
                        continue
                    rec.start_batch(f"runtime:{label}:{backend}:{flags}")
                    times = measure(rec, "runtime.csv", base,
                                    lambda bp=binary: timed([str(bp)]),
                                    check=lambda out, n=n: result_value(out) == n)
                    if times is None:
                        stopped[(backend, flags)] = f"skipped: the run at n={n} failed"
                    elif statistics.median(times) > SIZE_CAP_S:
                        stopped[(backend, flags)] = (f"skipped: a smaller n took more than "
                                                     f"{SIZE_CAP_S:.0f} s (median)")
    return 0


# ------------------------------------------------------------------------------------------------
# proof: residual cost of a proof argument (A/B pair)
# ------------------------------------------------------------------------------------------------


def cmd_proof(args):
    rec = Recorder(RESULTS, args.wait_max)
    work = Path(args.work_dir) / "proof"
    work.mkdir(parents=True, exist_ok=True)
    for (a, b) in PROOF_SIZES:
        calls = a * b
        bins = {}
        for variant in ("without", "with"):
            bins[variant] = build_variants(args, rec, f"proof_arg_{variant}.lrl",
                                           f"proof_arg_{variant}_c{calls}",
                                           {"A": str(a), "B": str(b)}, work)
        for backend in BACKENDS:
            for flags in FLAGS:
                pair = {v: bins[v].get((backend, flags)) for v in ("without", "with")}
                if None in pair.values():
                    print(f"  missing binary for {backend}/{flags}; skipped", flush=True)
                    continue
                rec.start_batch(f"proof:{backend}:{flags}")
                # Interleaved A/B: warm-up both, then ABBA order over args.proof_reps rounds.
                for v in ("without", "with"):
                    for w in range(WARMUP_FAST):
                        secs, rc, out, _err = timed([str(pair[v])])
                        la = loadavg()
                        rec.append("proof_arg.csv", {
                            "variant": v, "calls": calls, "backend": backend, "flags": flags,
                            "batch": rec.batch, "time": now_iso(), "warmup": 1, "rep": w,
                            "seconds": f"{secs:.6f}",
                            "status": "ok" if rc == 0 and result_value(out) == calls
                            else f"error:{rc}",
                            "load1": f"{la[0]:.2f}", "load5": f"{la[1]:.2f}",
                            "load15": f"{la[2]:.2f}"})
                for r in range(args.proof_reps):
                    order = ("without", "with") if r % 2 == 0 else ("with", "without")
                    for v in order:
                        secs, rc, out, _err = timed([str(pair[v])])
                        la = loadavg()
                        rec.append("proof_arg.csv", {
                            "variant": v, "calls": calls, "backend": backend, "flags": flags,
                            "batch": rec.batch, "time": now_iso(), "warmup": 0, "rep": r,
                            "seconds": f"{secs:.6f}",
                            "status": "ok" if rc == 0 and result_value(out) == calls
                            else f"error:{rc}",
                            "load1": f"{la[0]:.2f}", "load5": f"{la[1]:.2f}",
                            "load15": f"{la[2]:.2f}"})
                print(f"    proof {backend}/{flags}: done", flush=True)
    return 0


# ------------------------------------------------------------------------------------------------
# indexcost: compile-time evaluation of a closed size expression in a type index
# ------------------------------------------------------------------------------------------------


def cmd_indexcost(args):
    rec = Recorder(RESULTS, args.wait_max)
    work = Path(args.work_dir) / "indexcost"
    work.mkdir(parents=True, exist_ok=True)
    shim_env = make_shim(work)
    only = {int(x) for x in args.indexcost_n.split(",") if x}
    for (a, b) in INDEXCOST_SIZES:
        n = a * b
        if only and n not in only:
            continue
        for variant in ("vec_build_sum_closed_index", "vec_build_sum"):
            src = instantiate(PROGRAMS / f"{variant}.lrl", work / f"{variant}_n{n}.lrl",
                              SIZE=f"(nat_mul {a} {b})")
            rec.start_batch(f"indexcost:{variant}:{n}")

            def front(s=src):
                secs, rc, _gen, text = cli_compile(args.lrl, s, "typed", work / "ic.bin",
                                                   env=shim_env)
                return secs, rc, text, ""

            measure(rec, "indexcost.csv",
                    {"program": variant, "n": n, "backend": "typed",
                     "phase": "cli_front_noop_rustc"}, front)
    return 0


# ------------------------------------------------------------------------------------------------
# rustref: plain Rust reference (context only)
# ------------------------------------------------------------------------------------------------


def cmd_rustref(args):
    rec = Recorder(RESULTS, args.wait_max)
    work = Path(args.work_dir) / "rustref"
    work.mkdir(parents=True, exist_ok=True)
    src = PROGRAMS / "rust_reference" / "vec_rev_sum.rs"
    binary = work / "vec_rev_sum_ref.bin"
    secs, rc, _out, err = timed(["rustc", "-O", str(src), "-o", str(binary)])
    if rc != 0:
        print(err)
        return 1
    for mode in ("inplace", "snoc"):
        for n in RUST_REF_SIZES:
            rec.start_batch(f"rustref:{mode}:{n}")
            measure(rec, "rust_reference.csv", {"variant": mode, "n": n, "flags": "O"},
                    lambda m=mode, k=n: timed([str(binary), m, str(k)]),
                    check=lambda out, k=n: result_value(out) == k)
    return 0


# ------------------------------------------------------------------------------------------------
# summary
# ------------------------------------------------------------------------------------------------


def read_rows(name):
    path = RESULTS / name
    if not path.exists():
        return []
    with open(path, newline="") as fh:
        return list(csv.DictReader(fh))


def stats(values):
    return (statistics.median(values), min(values), max(values), len(values))


def fmt(s):
    if s is None:
        return "-"
    if s >= 100:
        return f"{s:.1f}"
    if s >= 1:
        return f"{s:.3f}"
    return f"{s:.4f}"


def excluded_batches():
    """Batches listed in results/excluded_batches.csv (batch,reason): their rows stay in the raw
    CSV files but are left out of every statistic; summary.md lists them with the reason."""
    return {r["batch"]: r["reason"] for r in read_rows("excluded_batches.csv")}


def group_times(rows, keys):
    excluded = excluded_batches()
    groups = {}
    for r in rows:
        if r.get("warmup") != "0" or r.get("status") != "ok" or r.get("batch") in excluded:
            continue
        groups.setdefault(tuple(r[k] for k in keys), []).append(float(r["seconds"]))
    return groups


def cmd_summary(_args):
    out = ["# LRL benchmark results (generated by `python3 bench/run_bench.py summary`)", ""]
    out.append("Wall-clock seconds measured with `time.perf_counter` around `subprocess.run` "
               "(output captured). Each cell: median / min / max over the stated number of "
               "measured runs (warm-up runs excluded). Raw data: `bench/results/*.csv`. "
               "Methodology and caveats: `bench/README.md`. These numbers describe this machine "
               "and this tree only; LRL makes no performance claims beyond them.")
    out.append("")
    machine = RESULTS / "machine.txt"
    if machine.exists():
        out += ["## Machine", "", "```", machine.read_text().strip(), "```", ""]

    # (1) compile time
    rows = read_rows("compile_time.csv")
    if rows:
        g = group_times(rows, ["program", "backend", "phase"])
        out += ["## 1. Compile time of the case studies", "",
                "`cli_total`: `lrl compile <file> --backend <b> -o <bin>` (front half + rustc as "
                "the CLI runs it). `cli_front_noop_rustc`: the same command with a no-op `rustc` "
                "first on PATH (it only creates the output file), i.e. the LRL front half "
                "(parse, expand, elaborate, kernel, MIR, Rust generation, file I/O). "
                "`rustc_cli_flags`: `rustc <generated>.rs -o <bin> -C incremental=<fresh dir>` "
                "(the CLI's flags). `rustc_O`: `rustc -O <generated>.rs -o <bin>`.", "",
                "| program | backend | phase | median s | min s | max s | runs |",
                "|---|---|---|---:|---:|---:|---:|"]
        for key in sorted(g):
            md, mn, mx, k = stats(g[key])
            out.append(f"| {key[0]} | {key[1]} | {key[2]} | {fmt(md)} | {fmt(mn)} | {fmt(mx)} "
                       f"| {k} |")
        out.append("")
        out += ["Split (medians): front half vs rustc with the CLI's flags; "
                "`front + rustc` is compared with the measured total.", "",
                "| program | backend | front s | rustc (CLI flags) s | front + rustc s | "
                "total s | front share of total | rustc -O s |",
                "|---|---|---:|---:|---:|---:|---:|---:|"]
        for prog in sorted({k[0] for k in g}):
            for be in BACKENDS:
                def med(ph):
                    v = g.get((prog, be, ph))
                    return statistics.median(v) if v else None
                f, rc, tot, ro = (med("cli_front_noop_rustc"), med("rustc_cli_flags"),
                                  med("cli_total"), med("rustc_O"))
                if None in (f, rc, tot):
                    continue
                out.append(f"| {prog} | {be} | {fmt(f)} | {fmt(rc)} | {fmt(f + rc)} | "
                           f"{fmt(tot)} | {100 * f / tot:.0f}% | {fmt(ro)} |")
        out.append("")
        gens = read_rows("generated_sources.csv")
        if gens:
            out += ["Generated Rust (last recorded copy): " + "; ".join(
                f"{r['program']} {r['backend']}: {r['lines']} lines, {r['bytes']} bytes"
                for r in {(r['program'], r['backend']): r for r in gens}.values()), ""]

    # (2) runtime
    rows = read_rows("runtime.csv")
    if rows:
        g = group_times(rows, ["workload", "n", "backend", "flags"])
        skipped = {(r["workload"], r["n"], r["backend"], r["flags"]): r["status"]
                   for r in rows if r["status"].startswith(("skipped", "build failed"))}
        failed = {(r["workload"], r["n"], r["backend"], r["flags"]): r["status"]
                  for r in rows if r["status"].startswith("error")}
        out += ["## 2. Run time of workloads derived from the case studies", "",
                "`cli`: the binary produced by `lrl compile` (rustc without -O). `O`: the same "
                "generated Rust rebuilt with `rustc -O <generated>.rs -o <bin>`. Every run's "
                "printed `Result:` was checked to equal n. Ratio = median(n) / median(previous n) "
                "(n doubles between rows, except where stated); exponent = log2(ratio) when n "
                "doubles.", ""]
        builds = read_rows("builds.csv")
        for wl in WORKLOADS:
            ns = sorted({int(k[1]) for k in list(g) + list(skipped) if k[0] == wl})
            if not ns:
                continue
            out += [f"### {wl}", "",
                    "| n | backend | flags | median s | min s | max s | runs | ratio to previous n "
                    "| exponent |", "|---:|---|---|---:|---:|---:|---:|---:|---:|"]
            for be in BACKENDS:
                for fl in FLAGS:
                    prev = None
                    prev_n = None
                    for n in ns:
                        key = (wl, str(n), be, fl)
                        if key in g:
                            md, mn, mx, k = stats(g[key])
                            ratio = exp = "-"
                            if prev is not None:
                                r_ = md / prev
                                ratio = f"{r_:.2f}"
                                if n == 2 * prev_n:
                                    exp = f"{math.log2(r_):.2f}"
                                else:
                                    exp = f"{math.log(r_) / math.log(n / prev_n):.2f} (n x{n / prev_n:g})"
                            out.append(f"| {n} | {be} | {fl} | {fmt(md)} | {fmt(mn)} | {fmt(mx)} "
                                       f"| {k} | {ratio} | {exp} |")
                            prev, prev_n = md, n
                        elif key in skipped:
                            out.append(f"| {n} | {be} | {fl} | - | - | - | 0 | {skipped[key]} | |")
                        elif key in failed:
                            out.append(f"| {n} | {be} | {fl} | - | - | - | 0 | {failed[key]} | |")
            out.append("")
        out += ["### Ratios of medians", "",
                "dynamic / typed at the same n and build; cli / O at the same n and backend. "
                "Only sizes measured in both configurations are listed.", "",
                "| workload | n | dynamic/typed (cli) | dynamic/typed (O) | typed cli/O | "
                "dynamic cli/O |", "|---|---:|---:|---:|---:|---:|"]
        for wl in WORKLOADS:
            if wl == "size_only":
                continue
            ns = sorted({int(k[1]) for k in g if k[0] == wl})
            for n in ns:
                m = {(be, fl): statistics.median(g[(wl, str(n), be, fl)])
                     for be in BACKENDS for fl in FLAGS if (wl, str(n), be, fl) in g}

                def ratio(a, b):
                    return f"{m[a] / m[b]:.1f}" if a in m and b in m else "-"
                cells = [ratio(('dynamic', 'cli'), ('typed', 'cli')),
                         ratio(('dynamic', 'O'), ('typed', 'O')),
                         ratio(('typed', 'cli'), ('typed', 'O')),
                         ratio(('dynamic', 'cli'), ('dynamic', 'O'))]
                if any(c != "-" for c in cells):
                    out.append(f"| {wl} | {n} | " + " | ".join(cells) + " |")
        out.append("")
        if builds:
            firsts = {f"{wl}_n{WORKLOAD_SIZES[wl][0][0] * WORKLOAD_SIZES[wl][0][1]}"
                      for wl in WORKLOADS}
            last = {}
            for r in builds:
                if r["status"] == "ok" and r["label"] in firsts:
                    last[(r["label"], r["backend"], r["flags"])] = r["binary_bytes"]
            if last:
                out += ["Binary sizes in bytes at the smallest n of each workload (`stat`; "
                        "the size hardly depends on n):", "",
                        "| program | typed cli | typed O | dynamic cli | dynamic O |",
                        "|---|---:|---:|---:|---:|"]
                for lab in sorted(firsts):
                    cells = [last.get((lab, be, fl), "-") for be in BACKENDS for fl in FLAGS]
                    out.append(f"| {lab} | " + " | ".join(str(c) for c in cells) + " |")
                out.append("")

    # (3) proof argument
    rows = read_rows("proof_arg.csv")
    if rows:
        g = group_times(rows, ["variant", "calls", "backend", "flags"])
        out += ["## 3. Residual cost of a proof argument", "",
                "`proof_arg_with.lrl` and `proof_arg_without.lrl` differ only in the `Eq` proof "
                "argument of `step` (called A*B times). Runs of the two binaries are interleaved "
                "(ABBA). Ratio = with / without. Extra per call = (median with - median "
                "without) / calls.", "",
                "| calls | backend | flags | without: median / min / max s | with: median / min / "
                "max s | runs (each) | ratio of medians | ratio of minima | extra per call ns |",
                "|---:|---|---|---|---|---:|---:|---:|---:|"]
        for calls in sorted({k[1] for k in g}, key=int):
            for be in BACKENDS:
                for fl in FLAGS:
                    a = g.get(("without", calls, be, fl))
                    b = g.get(("with", calls, be, fl))
                    if not a or not b:
                        continue
                    sa, sb = stats(a), stats(b)
                    out.append(f"| {calls} | {be} | {fl} | {fmt(sa[0])} / {fmt(sa[1])} / "
                               f"{fmt(sa[2])} | {fmt(sb[0])} / {fmt(sb[1])} / {fmt(sb[2])} | "
                               f"{min(sa[3], sb[3])} | {sb[0] / sa[0]:.3f} | {sb[1] / sa[1]:.3f} | "
                               f"{1e9 * (sb[0] - sa[0]) / int(calls):.0f} |")
        out.append("")

    # (4) Rust reference
    rows = read_rows("rust_reference.csv")
    if rows:
        g = group_times(rows, ["variant", "n"])
        out += ["## 4. Context only: plain Rust reference for vec_rev_sum", "",
                "`bench/programs/rust_reference/vec_rev_sum.rs`, built with `rustc -O`. "
                "`inplace`: `Vec<u64>` of n ones, `reverse()` in place, sum. `snoc`: the same "
                "algorithm as the case study's `vreverse` (one new vector per `vsnoc`, copying). "
                "Factor = LRL median / Rust median at the same n. This is a reference point only.",
                "", "| n | variant | median s | min s | max s | runs | factor typed/O | "
                "factor dynamic/O |", "|---:|---|---:|---:|---:|---:|---:|---:|"]
        rt = group_times(read_rows("runtime.csv"), ["workload", "n", "backend", "flags"])
        for key in sorted(g, key=lambda k: (k[0], int(k[1]))):
            md, mn, mx, k = stats(g[key])
            fac = []
            for be in BACKENDS:
                v = rt.get(("vec_rev_sum", key[1], be, "O"))
                if v:
                    x = statistics.median(v) / md
                    fac.append(f"{x:.1f}" if x < 10 else f"{x:.0f}")
                else:
                    fac.append("-")
            out.append(f"| {key[1]} | {key[0]} | {fmt(md)} | {fmt(mn)} | {fmt(mx)} | {k} | "
                       f"{fac[0]} | {fac[1]} |")
        out.append("")

    # (5) compile-time evaluation of indices
    rows = read_rows("indexcost.csv")
    if rows:
        g = group_times(rows, ["program", "n"])
        out += ["## 5. Compile time: a closed size expression in a type index", "",
                "Front half of `lrl compile --backend typed` (no-op `rustc` on PATH) for "
                "`vec_build_sum_closed_index.lrl` (`main` = `(vsum (vbuild size))`, so `size` "
                "occurs in the type index `Vec Nat size`) and `vec_build_sum.lrl` (`main` = "
                "`(workload size)`, the index is the variable n inside `workload`). Both compute "
                "the same value at run time.", "",
                "| n | closed index: median / min / max s (runs) | index is a variable: median / "
                "min / max s (runs) |", "|---:|---|---|"]
        for n in sorted({int(k[1]) for k in g}):
            cells = []
            for prog in ("vec_build_sum_closed_index", "vec_build_sum"):
                v = g.get((prog, str(n)))
                if v:
                    md, mn, mx, k = stats(v)
                    cells.append(f"{fmt(md)} / {fmt(mn)} / {fmt(mx)} ({k})")
                else:
                    cells.append("-")
            out.append(f"| {n} | {cells[0]} | {cells[1]} |")
        out.append("")

    batches = [b for b in read_rows("batches.csv") if b["batch"] not in excluded_batches()]
    if batches:
        busy = [b for b in batches if b["busy_processes"] != "none"]
        loads = [float(b["uptime"].split("load averages:")[-1].split()[0]) for b in batches
                 if "load averages:" in b["uptime"]]
        tops = sorted({m.group(2) for b in batches
                       for m in re.finditer(r"(\d+):(.*?):([0-9.]+)%", b["top_cpu_processes"])})
        run_loads = [float(r["load1"]) for name in ("compile_time.csv", "runtime.csv",
                                                    "proof_arg.csv", "rust_reference.csv",
                                                    "indexcost.csv")
                     for r in read_rows(name)
                     if r.get("load1") and r.get("batch") not in excluded_batches()]
        out += ["## Measurement conditions", "",
                f"- {len(batches)} measurement batches (excluded batches not counted); batches "
                f"started while a compiler/prover/"
                f"LRL process was running: {len(busy)}.",
                f"- 1-minute load average at batch start (`uptime`): min {min(loads):.2f}, "
                f"median {statistics.median(loads):.2f}, max {max(loads):.2f}." if loads else "",
                f"- 1-minute load average recorded after each run (all CSV rows, warm-up "
                f"included): min {min(run_loads):.2f}, median {statistics.median(run_loads):.2f}, "
                f"max {max(run_loads):.2f} over {len(run_loads)} runs." if run_loads else "",
                f"- Processes recorded at some batch start among the (at most three) busiest "
                f"processes using >= 10% CPU (`ps -A -r`, other than the driver): "
                f"{', '.join(tops) if tops else 'none'}."]
    spreads = []
    for name, keys in (("compile_time.csv", ["program", "backend", "phase"]),
                       ("runtime.csv", ["workload", "n", "backend", "flags"]),
                       ("proof_arg.csv", ["variant", "calls", "backend", "flags"]),
                       ("rust_reference.csv", ["variant", "n"]),
                       ("indexcost.csv", ["program", "n"])):
        for key, v in group_times(read_rows(name), keys).items():
            spreads.append((max(v) / min(v) - 1.0, statistics.median(v), name, key))
    if spreads:
        sp = sorted(x[0] for x in spreads)
        long_ = sorted(x[0] for x in spreads if x[1] >= 0.1)
        worst = max(spreads)
        out += [f"- Spread of a configuration = max / min - 1 over its measured runs. All "
                f"{len(sp)} configurations: median {100 * statistics.median(sp):.1f}%, "
                f"max {100 * worst[0]:.1f}% ({worst[2]} {' '.join(worst[3])}, median "
                f"{fmt(worst[1])} s)."]
        if long_:
            out += [f"- Configurations with a median of at least 0.1 s ({len(long_)}): spread "
                    f"median {100 * statistics.median(long_):.1f}%, max {100 * max(long_):.1f}%; "
                    f"{sum(1 for x in long_ if x <= 0.10)} of them have a spread of at most 10%."]
        out.append("")
    excluded = excluded_batches()
    if excluded:
        out += ["## Excluded batches", "",
                "Rows of these batches remain in the raw CSV files but are not used above.", "",
                "| batch | reason |", "|---|---|"]
        out += [f"| {b} | {why} |" for b, why in excluded.items()]
        out.append("")
    (RESULTS / "summary.md").write_text("\n".join(out) + "\n")
    print(f"wrote {RESULTS / 'summary.md'}")
    return 0


# ------------------------------------------------------------------------------------------------


def main():
    global RESULTS
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("command",
                    choices=["check", "machine", "compile", "runtime", "proof", "rustref",
                             "indexcost", "summary", "all"])
    ap.add_argument("--lrl", default=os.environ.get("LRL_BIN"),
                    help="LRL CLI binary (a release build; default $LRL_BIN)")
    ap.add_argument("--work-dir", default=str(BENCH / "work"),
                    help="directory for instantiated programs, generated Rust and binaries")
    ap.add_argument("--workloads", default="", help="comma-separated subset for `runtime`")
    ap.add_argument("--indexcost-n", default="",
                    help="comma-separated subset of the n values of `indexcost` (default: all)")
    ap.add_argument("--proof-reps", type=int, default=15,
                    help="interleaved rounds for `proof` (each round runs both binaries)")
    ap.add_argument("--wait-max", type=float, default=600.0,
                    help="seconds to wait for busy processes before a batch")
    ap.add_argument("--results-dir", default=str(RESULTS),
                    help="where CSV files and summary.md are written (default bench/results)")
    args = ap.parse_args()
    RESULTS = Path(args.results_dir).resolve()
    if args.command in ("compile", "runtime", "proof", "indexcost", "all") and not args.lrl:
        ap.error("--lrl (or $LRL_BIN) is required")
    if args.command in ("compile", "runtime", "proof", "rustref", "indexcost", "all"):
        check_stack()
    if args.lrl:
        args.lrl = str(Path(args.lrl).resolve())
    commands = {
        "check": cmd_check, "machine": cmd_machine, "compile": cmd_compile,
        "runtime": cmd_runtime, "proof": cmd_proof, "rustref": cmd_rustref,
        "indexcost": cmd_indexcost, "summary": cmd_summary,
    }
    if args.command == "all":
        for name in ("check", "machine", "compile", "runtime", "proof", "rustref", "indexcost",
                     "summary"):
            rc = commands[name](args)
            if rc:
                return rc
        return 0
    return commands[args.command](args)


if __name__ == "__main__":
    sys.exit(main())
