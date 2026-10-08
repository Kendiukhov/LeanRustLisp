#!/usr/bin/env python3
"""Collect every artifact figure quoted in the paper and write numbers.tex.

Run from the repository root:

    python3 paper/jot_r1/scripts/collect_numbers.py --test-log <log of `cargo test --all --no-fail-fast`>

Every value is computed by a shell command or by parsing a file that a script in the repository
generates. The commands and raw results are written to paper/jot_r1/numbers_provenance.md, which the
audit log references. macOS AppleDouble files (`._*`) are excluded from every count.
"""
import argparse
import os
import re
import shutil
import subprocess
import sys

ROOT = os.getcwd()
OUT_TEX = os.path.join(ROOT, "paper/jot_r1/numbers.tex")
OUT_PROV = os.path.join(ROOT, "paper/jot_r1/numbers_provenance.md")
values = []      # (macro, value, how)


def sh(cmd):
    return subprocess.run(cmd, shell=True, cwd=ROOT, capture_output=True, text=True, check=True).stdout.strip()


def put(macro, value, how):
    values.append((macro, value, how))


def fmt_int(n):
    n = int(n)
    return f"{n:,}".replace(",", "\\,") if n >= 10000 else str(n)


def rust_lines(paths):
    cmd = f"find {paths} -name '*.rs' -not -name '._*' -type f -print0 | xargs -0 cat | wc -l"
    return int(sh(cmd)), cmd


def rust_files(paths):
    cmd = f"find {paths} -name '*.rs' -not -name '._*' -type f | wc -l"
    return int(sh(cmd)), cmd


def strip_test_modules(text):
    """Remove `#[cfg(test)]`-gated items (modules or functions) by brace matching.

    An item that ends with `;` before any `{` (for example `mod test_support;`) is removed up to and
    including that line only.
    """
    out, i = [], 0
    lines = text.split("\n")
    while i < len(lines):
        if lines[i].strip().startswith("#[cfg(test)]"):
            depth, seen = 0, False
            first = True
            while i < len(lines):
                line = lines[i]
                if first:
                    # the attribute line itself; the item starts after it
                    rest = line.strip()[len("#[cfg(test)]"):]
                    first = False
                else:
                    rest = line
                if not seen and ";" in rest and ("{" not in rest or rest.index(";") < rest.index("{")):
                    i += 1
                    break
                depth += rest.count("{") - rest.count("}")
                seen = seen or "{" in rest
                i += 1
                if seen and depth <= 0:
                    break
            continue
        out.append(lines[i])
        i += 1
    return out


def lean_imported_files(root_file):
    """Files reachable from root_file through `import LRL...` lines (root_file included)."""
    base = os.path.join(ROOT, "mechanization/src")
    seen, todo = [], [root_file]
    while todo:
        f = todo.pop()
        if f in seen:
            continue
        seen.append(f)
        for line in open(os.path.join(ROOT, f)):
            m = re.match(r"import (LRL[\w.]*)", line)
            if m:
                todo.append("mechanization/src/" + m.group(1).replace(".", "/") + ".lean")
    return sorted(seen)


TEST_INPUT_PATHS = ("kernel frontend mir cli codegen stdlib tests code_examples Cargo.toml Cargo.lock docs/spec "
                    "':(glob)case_studies/**/manifest.tsv' "
                    "':(glob)case_studies/**/*.lrl' ':(glob)case_studies/**/*.rs' ':(glob)case_studies/**/Cargo.toml'")
TEST_SUMMARY = "paper/jot_r1/test_summary.txt"
ARTIFACT_PATHS = ("kernel frontend mir cli codegen stdlib case_studies bench mechanization tests "
                  "code_examples Cargo.toml Cargo.lock")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--test-log", required=True,
                    help="log of `cargo test --all --no-fail-fast` whose first line is `revision: <git rev-parse HEAD>`")
    ap.add_argument("--allow-dirty", action="store_true",
                    help="for drafts only: write TODO-PIN-COMMIT instead of failing on a dirty tree")
    args = ap.parse_args()

    commit = sh("git rev-parse HEAD 2>/dev/null")
    dirty_cmd = f"git status --porcelain --untracked-files=all -- {ARTIFACT_PATHS} | grep -v '/\\._' || true"
    dirty = sh(dirty_cmd)
    if dirty and not args.allow_dirty:
        sys.exit("error: the artifact paths have uncommitted changes; commit them first:\n" + dirty[:2000])

    crates = ["kernel", "frontend", "mir", "cli", "codegen"]
    total, cmd = rust_lines(" ".join(crates))
    put("NumRustLines", fmt_int(total), cmd)
    nfiles, cmd = rust_files(" ".join(crates))
    put("NumRustFiles", str(nfiles), cmd)
    for c in crates:
        cap = c.capitalize()
        s, cmd = rust_lines(f"{c}/src")
        put(f"Num{cap}SrcLines", fmt_int(s), cmd)
        if os.path.isdir(os.path.join(ROOT, c, "tests")):
            t, cmd = rust_lines(f"{c}/tests")
        else:
            t, cmd = 0, f"(no {c}/tests directory)"
        put(f"Num{cap}TestLines", fmt_int(t), cmd)

    # Kernel without in-crate tests: drop test_support.rs and #[cfg(test)] items.
    kept = 0
    for f in sorted(sh("find kernel/src -name '*.rs' -not -name '._*' -type f").split("\n")):
        if f.endswith("test_support.rs"):
            continue
        with open(os.path.join(ROOT, f)) as fh:
            kept += len(strip_test_modules(fh.read().rstrip("\n")))
    put("NumKernelNonTestLines", fmt_int(kept),
        "kernel/src/*.rs without test_support.rs and without #[cfg(test)] items (scripts/collect_numbers.py:strip_test_modules)")

    n_test_fns = int(sh("grep -rh --include='*.rs' -E '^\\s*#\\[test\\]' kernel frontend mir cli codegen | wc -l"))
    put("NumTestFns", str(n_test_fns), "grep -rh --include='*.rs' -E '^\\s*#\\[test\\]' kernel frontend mir cli codegen | wc -l")
    passed = failed = ignored = 0
    summary_lines = []
    with open(args.test_log) as fh:
        first = fh.readline().strip()
        if not args.allow_dirty:
            # The tests must have run on a revision whose code and test inputs equal HEAD's
            # (HEAD may differ from it only in results files).
            m = re.fullmatch(r"revision: ([0-9a-f]{40})", first)
            if not m:
                sys.exit(f"error: {args.test_log} must start with 'revision: <sha>', found '{first}'")
            same = subprocess.run(f"git diff --quiet {m.group(1)} HEAD -- {TEST_INPUT_PATHS}", shell=True, cwd=ROOT).returncode == 0
            if not same:
                sys.exit(f"error: code or test inputs differ between the tested revision {m.group(1)} and HEAD")
        summary_lines.append(first)
        for line in fh:
            if line.lstrip().startswith(("Running ", "Doc-tests ", "command: ")):
                # drop the local path of the test binary: "Running tests/x.rs (/.../deps/x-hash)"
                summary_lines.append(re.sub(r" \(/[^)]*\)$", "", line.rstrip()))
            m = re.match(r"test result: \w+\. (\d+) passed; (\d+) failed; (\d+) ignored", line)
            if m:
                summary_lines.append(line.rstrip())
                passed += int(m.group(1)); failed += int(m.group(2)); ignored += int(m.group(3))
    # Keep the evidence for the test counts in the repository.
    with open(os.path.join(ROOT, TEST_SUMMARY), "w") as fh:
        fh.write("\n".join(summary_lines) + "\n")
    put("NumTestsPassed", str(passed), f"sum of 'test result' lines in {TEST_SUMMARY} (extracted from the cargo test log)")
    put("NumTestsFailed", str(failed), f"sum of 'test result' lines in {TEST_SUMMARY}")
    put("NumTestsIgnored", str(ignored), f"sum of 'test result' lines in {TEST_SUMMARY}")

    lrl_cmd = ("find tests code_examples stdlib case_studies -name '*.lrl' -not -name '._*' -type f | wc -l")
    put("NumLrlFiles", sh(lrl_cmd), lrl_cmd)

    for name in ["vectors", "protocol"]:
        cmd = f"wc -l < case_studies/lrl/{name}.lrl"
        put(f"Num{name.capitalize()}Lines", sh(cmd).strip(), cmd)
    cmd = "grep -c '^THEOREM ' case_studies/lrl/results_vectors.md"
    put("NumVectorsTheorems", sh(cmd), cmd)
    cmd = "find case_studies/lrl/neg -name '*.lrl' -not -name '._*' | wc -l"
    put("NumCaseNegatives", sh(cmd), cmd)

    # Validation corpus.
    rows = [l.split("\t") for l in open(os.path.join(ROOT, "case_studies/corpus/manifest.tsv"))
            if l.strip() and not l.startswith("#") and not l.startswith("class\t")]
    put("NumCorpusClasses", str(sum(1 for r in rows if r[1] != "positive")), "manifest.tsv rows with kind != positive")
    put("NumCorpusPositives", str(sum(1 for r in rows if r[1] == "positive")), "manifest.tsv rows with kind == positive")
    cmd = "find case_studies/corpus -name '*.lrl' -not -name '._*' | wc -l"
    put("NumCorpusFiles", sh(cmd), cmd)
    res = open(os.path.join(ROOT, "case_studies/corpus/results_corpus.md")).read()
    m = re.search(r"\*\*(\d+) of (\d+) manifest rows match", res)
    put("NumCorpusMatch", m.group(1), "results_corpus.md headline")
    put("NumCorpusRows", m.group(2), "results_corpus.md headline")

    # Comparison.
    for key, f in [("LeanIdris", "results_lean_idris.md"), ("RustRacket", "results_rust_racket.md"),
                   ("Lrl", "results_lrl.md")]:
        txt = open(os.path.join(ROOT, "case_studies/comparison", f)).read()
        m = re.search(r"## Results \((\d+) of (\d+) cases match", txt)
        put(f"NumCmp{key}Cases", m.group(2), f"{f} headline")
        put(f"NumCmp{key}Match", m.group(1), f"{f} headline")
    for lang, ext in [("lean", "lean"), ("idris2", "idr"), ("rust", "rs"), ("racket", "rkt"), ("lrl", "lrl")]:
        cmd = f"find case_studies/comparison/{lang} -name '*.{ext}' -not -name '._*' | wc -l"
        put(f"NumCmpFiles{lang.capitalize().replace('2', 'Two')}", sh(cmd), cmd)


    # Stage matrix (case_studies/tools/results_stage_matrix.md).
    sm = open(os.path.join(ROOT, "case_studies/tools/results_stage_matrix.md")).read()
    for key, label in [("Both", "kernel and MIR both reject"), ("KernelOnly", "kernel rejects, MIR does not"),
                       ("MirOnly", "MIR only (kernel accepts)"), ("Elab", "elaborator or expander only (no core term)"),
                       ("Decl", "declaration-level (inductive) check"), ("Boundary", "macro boundary at expansion")]:
        m = re.search(re.escape("**" + label) + r"[^\n]*?\((\d+) classes?\)", sm)
        put(f"NumStageCorpus{key}", m.group(1), f"results_stage_matrix.md, section 1 summary: '{label}'")
    sec = sm[sm.index("## 2. Program corpus"):sm.index("## 3. Program corpus")]
    m = re.search(r"(\d+) files \((\d+) rejected as a whole[^)]*\), (\d+) definitions and (\d+) top-level expressions", sec)
    put("NumStageFiles", m.group(1), "results_stage_matrix.md section 2 (dynamic prelude)")
    put("NumStageDefs", m.group(3), "results_stage_matrix.md section 2 (dynamic prelude)")
    put("NumStageExprs", m.group(4), "results_stage_matrix.md section 2 (dynamic prelude)")
    for key, label in [("Elab", "elaboration"), ("KTyping", "kernel typing"), ("KAdmit", "kernel admission (add_definition)"),
                       ("KOwn", "kernel ownership walk"), ("MLower", "MIR lowering"), ("MTyping", "MIR typing"),
                       ("MOwn", "MIR ownership"), ("MBorrow", "MIR borrow check (NLL)"), ("Cli", "CLI admits (replay)")]:
        m = re.search(r"\| " + re.escape(label) + r" \| (\d+) \| (\d+) \| (\d+) \|", sec)
        put(f"NumStage{key}Pass", m.group(1), f"results_stage_matrix.md section 2, row '{label}'")
        put(f"NumStage{key}Reject", m.group(2), f"results_stage_matrix.md section 2, row '{label}'")
    m = re.search(r"\*\*Kernel accepts, MIR rejects\*\* \((\d+) definitions?\)", sec)
    put("NumStageKAcceptMReject", m.group(1), "results_stage_matrix.md section 2")
    kam = sec[sec.index("**Kernel accepts, MIR rejects**"):sec.index("**Kernel rejects, MIR accepts**")]
    kam_groups = re.findall(r"^- (.*?):", kam, re.M)
    kam_items = re.findall(r"^  - .*$", kam, re.M)
    m = re.search(r"\*\*Kernel rejects, MIR accepts\*\* \((\d+) definitions?\)", sec)
    put("NumStageKRejectMAccept", m.group(1), "results_stage_matrix.md section 2")
    m = re.search(r"for (\d+) of (\d+) files the multiset of diagnostic codes", sm)
    put("NumStageCliAgree", m.group(1), "results_stage_matrix.md cross-check")
    put("NumStageCliFiles", m.group(2), "results_stage_matrix.md cross-check")
    sec0 = sm[sm.index("## 0."):sm.index("## 1.")]
    sec0_rows = re.findall(r"^\| (dynamic|typed) \| (\w+) \| (\d+) \| (\d+) \| (\d+) \| (\d+) \| (\d+) \| (\d+) \|$", sec0, re.M)


    # Measurements (bench/results/summary.md, generated by bench/run_bench.py summary).
    bs = open(os.path.join(ROOT, "bench/results/summary.md")).read()
    src = "bench/results/summary.md"
    def comp(prog, backend, phase):
        m = re.search(r"\| case_studies/lrl/" + prog + r"\.lrl \| " + backend + r" \| " + phase + r" \| ([0-9.]+) \|", bs)
        return m.group(1)
    for prog in ["vectors", "protocol"]:
        for backend in ["typed", "dynamic"]:
            P, B = prog.capitalize(), backend.capitalize()
            put(f"Bench{P}{B}Total", comp(prog, backend, "cli_total"), f"{src}: {prog} {backend} cli_total median")
            put(f"Bench{P}{B}Front", comp(prog, backend, "cli_front_noop_rustc"), f"{src}: {prog} {backend} front-half median")
            put(f"Bench{P}{B}RustcO", comp(prog, backend, "rustc_O"), f"{src}: {prog} {backend} rustc -O median")
    def rt(workload, n, backend, flags):
        sec = bs[bs.index("### " + workload):]
        sec = sec[:sec.index("\n### ", 5)] if "\n### " in sec[5:] else sec
        m = re.search(r"\| " + str(n) + r" \| " + backend + r" \| " + flags + r" \| ([0-9.]+) \|", sec)
        return m.group(1)
    for wl, n in [("vec_build_sum", 4000), ("list_fold", 32000), ("proto_send", 4000), ("vec_rev_sum", 400)]:
        key = "".join(w.capitalize() for w in wl.split("_"))
        put(f"Bench{key}N", fmt_int(n), f"{src}: chosen size for {wl}")
        for backend in ["typed", "dynamic"]:
            for flags in ["cli", "O"]:
                put(f"Bench{key}{backend.capitalize()}{flags.capitalize()}", rt(wl, n, backend, flags),
                    f"{src}: {wl} n={n} {backend} {flags} median")
    rows = re.findall(r"\| (\d+) \| (typed|dynamic) \| (cli|O) \| [^|]+\| [^|]+\| \d+ \| ([0-9.]+) \| ([0-9.]+) \| (\d+) \|", bs)
    def rng(vals):
        lo, hi = f"{min(vals):.2f}", f"{max(vals):.2f}"
        return lo if lo == hi else f"{lo}--{hi}"
    for backend in ["typed", "dynamic"]:
        for flags in ["cli", "O"]:
            sel = [r for r in rows if r[1] == backend and r[2] == flags]
            put(f"BenchProof{backend.capitalize()}{flags.capitalize()}Ratio", rng([float(r[3]) for r in sel]),
                f"{src} section 3: ratio of medians, {backend} {flags}")
            ns = sorted(int(r[5]) for r in sel)
            put(f"BenchProof{backend.capitalize()}{flags.capitalize()}Ns", f"{ns[0]}--{ns[-1]}" if ns[0] != ns[-1] else str(ns[0]),
                f"{src} section 3: extra ns per call, {backend} {flags}")
    ci = re.findall(r"\| (\d+) \| ([0-9.]+) / [0-9.]+ / [0-9.]+ \(\d+\) \| ([0-9.]+) / [0-9.]+ / [0-9.]+ \(\d+\) \|", bs)
    letters = {"250": "A", "500": "B", "1000": "C", "2000": "D"}
    for n, closed, var in ci:
        put(f"BenchClosedIndex{letters[n]}", closed, f"{src} section 5: closed index n={n}")
        put(f"BenchVarIndex{letters[n]}", var, f"{src} section 5: variable index n={n}")
    var_vals = [float(var) for _n, _c, var in ci]
    put("BenchVarIndexRange", f"{min(var_vals):.3f}--{max(var_vals):.3f}" if var_vals else "TODO",
        f"{src} section 5: minimum and maximum of the variable-index medians")

    # Mechanization: only the files that `lake build LRL` builds (reachable from src/LRL.lean).
    lean_files = lean_imported_files("mechanization/src/LRL.lean")
    cmd = "cat " + " ".join(lean_files) + " | wc -l"
    put("NumLeanLines", fmt_int(sh(cmd)), cmd)
    put("NumLeanFiles", str(len(lean_files)), "files reachable from mechanization/src/LRL.lean by `import LRL...`")
    cmd = "find mechanization/src/LRL/Affine -name '*.lean' -not -name '._*' -print0 | xargs -0 cat | wc -l"
    put("NumAffineLines", fmt_int(sh(cmd)), cmd)
    cmd = "cat mechanization/src/LRL/Affine/*.lean | grep -cE '^(theorem|lemma) '"
    put("NumAffineTheorems", sh(cmd), cmd)
    cmd = "cat mechanization/lean-toolchain"
    put("LeanToolchain", sh(cmd).split(":")[-1], cmd)

    # Tool versions recorded in the comparison results files.
    li = open(os.path.join(ROOT, "case_studies/comparison/results_lean_idris.md")).read()
    rr = open(os.path.join(ROOT, "case_studies/comparison/results_rust_racket.md")).read()
    put("ToolLean", re.search(r"Lean \(version ([0-9.]+)", li).group(1), "results_lean_idris.md header (lean --version)")
    put("ToolIdris", re.search(r"Idris 2, version ([0-9.]+)", li).group(1), "results_lean_idris.md header (idris2 --version)")
    put("ToolRustc", re.search(r"rustc ([0-9.]+) \(", rr).group(1), "results_rust_racket.md header (rustc -vV)")
    put("ToolRacket", re.search(r"Racket v([0-9.]+)", rr).group(1), "results_rust_racket.md header (racket --version)")
    bench_rustc = re.search(r"rustc ([0-9.]+) \(", bs).group(1)
    if bench_rustc != re.search(r"rustc ([0-9.]+) \(", rr).group(1):
        sys.exit("error: bench and comparison used different rustc versions; the paper names one")

    # Stage matrix probe files and bench extras.
    m = re.search(r"\| dynamic \| mir_gaps \| (\d+) \|", sm)
    put("NumStageProbeFiles", m.group(1), "results_stage_matrix.md section 0, row 'dynamic | mir_gaps'")
    m = re.search(r"stack soft limit for measured processes \(ulimit -s, KiB\): (\d+)", bs)
    put("BenchStackKiB", fmt_int(m.group(1)), f"{src}: machine block, ulimit -s")
    ratios = []
    for wl, n in [("vec_build_sum", 4000), ("proto_send", 4000), ("vec_rev_sum", 400)]:
        m = re.search(r"\| " + wl + r" \| " + str(n) + r" \| ([0-9.]+) \| ([0-9.]+) \|", bs)
        ratios += [float(m.group(1)), float(m.group(2))]
    put("BenchDynTypedRatioRange", f"{min(ratios):.0f}--{max(ratios):.0f}",
        f"{src} 'Ratios of medians': dynamic/typed (cli and O) for vec_build_sum 4000, proto_send 4000, vec_rev_sum 400")

    pinned = commit if not dirty else "TODO-PIN-COMMIT"
    put("PinnedCommit", pinned, "git rev-parse HEAD (clean artifact paths required)")
    put("PinnedCommitShort", pinned[:10], "git rev-parse HEAD (clean artifact paths required)")

    # Copies of the case studies for Appendix B, so that the paper builds outside the repository.
    os.makedirs(os.path.join(ROOT, "paper/jot_r1/listings"), exist_ok=True)
    for name in ["vectors", "protocol"]:
        shutil.copyfile(os.path.join(ROOT, f"case_studies/lrl/{name}.lrl"),
                        os.path.join(ROOT, f"paper/jot_r1/listings/{name}.lrl"))

    # The text states that every one of these checks passed; refuse to write numbers that contradict it.
    v = {macro: value for macro, value, _ in values}
    problems = []
    def need(cond, what):
        if not cond:
            problems.append(what)
    need(v["NumCorpusMatch"] == v["NumCorpusRows"], "corpus: not every manifest row matches")
    for key in ["LeanIdris", "RustRacket", "Lrl"]:
        need(v[f"NumCmp{key}Match"] == v[f"NumCmp{key}Cases"], f"comparison {key}: not every case matches")
    need(v["NumTestsFailed"] == "0" and v["NumTestsIgnored"] == "0", "tests: failed or ignored tests")
    need(v["NumStageCliAgree"] == v["NumStageCliFiles"], "stage matrix: CLI cross-check disagrees")
    need(len(sec0_rows) > 0 and all(r[6] == "0" and r[7] == "0" for r in sec0_rows),
         "stage matrix: harness self-check has inconsistent or crashed records")
    need(v["NumStageKRejectMAccept"] == "0", "stage matrix: the kernel rejects a definition that MIR accepts")
    need(all(g.startswith("loan errors only") for g in kam_groups) and len(kam_items) == int(v["NumStageKAcceptMReject"])
         and all("(expected negative)" in it for it in kam_items)
         and set(re.findall(r"M\d{3}", " ".join(kam_groups))) <= {"M200", "M203"},
         "stage matrix: a kernel-accepts/MIR-rejects definition is not a borrow error (M200/M203) in a negative test")
    if problems:
        msg = "\n".join("  - " + p for p in problems)
        if args.allow_dirty:
            print("WARNING (draft mode):\n" + msg, file=sys.stderr)
        else:
            sys.exit("error: the results contradict statements in the paper:\n" + msg)

    with open(OUT_TEX, "w") as fh:
        fh.write("% Generated by paper/jot_r1/scripts/collect_numbers.py; do not edit by hand.\n")
        for macro, value, _ in values:
            fh.write(f"\\newcommand{{\\{macro}}}{{{value}}}\n")
    with open(OUT_PROV, "w") as fh:
        fh.write("# Provenance of the figures in numbers.tex\n\n")
        fh.write("Generated from the repository root by\n\n"
                 f"    python3 paper/jot_r1/scripts/collect_numbers.py --test-log <log of `cargo test --all --no-fail-fast`>\n\n"
                 f"The test counts come from {TEST_SUMMARY}, which the script extracts from that log "
                 "(its first line records the tested revision).\n\n")
        fh.write("| macro | value | command or source |\n|---|---|---|\n")
        for macro, value, how in values:
            fh.write(f"| `\\{macro}` | {value} | `{how}` |\n")
    print(f"wrote {OUT_TEX} ({len(values)} values) and {OUT_PROV}")


if __name__ == "__main__":
    sys.exit(main())
