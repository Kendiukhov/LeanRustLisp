#!/usr/bin/env python3
"""Summarise stage-matrix JSON lines into results_stage_matrix.md.

Usage: summarize.py --results <dir with <backend>/<set>.jsonl> --root <repo root> --out <md file>
                    [--command "<command line recorded in the header>"]
                    [--tool-sha256 <hex>] [--cli-sha256 <hex>]

--tool-sha256 / --cli-sha256: SHA-256 of the stage_matrix tool binary and of the CLI binary used for the
cross-check (check_against_cli.py), computed by run_stage_matrix.sh; recorded in the header next to the
repository commit.

Everything in the generated file is computed from the JSON lines, except the short cause notes in
CAUSE_NOTES below, which were written after inspecting the MIR of the named definitions
(`stage_matrix --dump-mir <def> <file>`) and the cited source files; a divergence without a note
is printed as "(not analysed)".
"""
import argparse
import collections
import datetime
import json
import os
import re
import subprocess

# Hand-written cause notes for divergent definitions, keyed by (file basename, definition name).
# Each note names the mechanism, labelled (a)-(e) as in case_studies/tools/stage_matrix/README.md (evidence there).
CAUSE_NOTES = {
    # kernel rejects, MIR (on the same elaborated term) accepts
    ("03_call_moved_function.lrl", "use_after"):
        "(a) MIR move tracking used to skip function values (`check_operand_moves`, mir/src/analysis/ownership.rs); "
        "fixed: moves of Fn/FnMut values by assignment or argument are tracked",
    ("03_call_moved_function_macro.lrl", "use_after"):
        "(a) same as the hand-written version",
    ("25_borrow_after_move.lrl", "bam"):
        "(b) MIR ownership used to check only `Rvalue::Use` operands (`check_rvalue_structured`); fixed: borrows "
        "and discriminant reads of a moved place are uses after move",
    ("25_borrow_after_move_macro.lrl", "bam"):
        "(b) same as the hand-written version",
    ("09_fix_consumes_capture.lrl", "loop_eat"):
        "(c) the fixpoint body reads its captures with `copy _1.k` from an env local typed `()` [copy], so a "
        "non-Copy capture is copied on every recursive call without M101/M100",
    ("09_fix_consumes_capture_macro.lrl", "loop_eat"):
        "(c) same as the hand-written version (fixpoint captures read by copy)",
    # MIR-independence probes (case_studies/tools/stage_matrix/gaps/)
    ("g1_borrow_after_move.lrl", "bam"):
        "(b) regression probe: `check_rvalue_structured` used to check only `Rvalue::Use` (`_7 = &_2` after "
        "`_5 = move _2` passed); borrows of moved places are now checked",
    ("g2_moved_fn_value_called.lrl", "twice"):
        "(a) regression probe: `check_operand_moves` used to skip moves of Fn/FnMut function values; now tracked "
        "(except inside a closure literal's captures, where lowering moves read-only function values)",
    ("g3_fix_consumes_capture.lrl", "loop_eat"):
        "(c) open: fixpoint captures are read with `copy _1.k` from an env local typed `()` [copy]; MIR does not "
        "re-check closure kinds (how often a body runs), as for Fn closures (corpus 05)",
    ("g4_dispatched_minor_consumes_capture.lrl", "spread"):
        "(d) regression probe: an arm that does not use its non-Copy recursive field used to pass the FnOnce minor-premise "
        "closure once to the recursor entry function (repeated calls outside MIR); entry dispatch now requires a Copy minor",
    ("g5_copy_marked_fnonce_local.lrl", "f"):
        "(e) regression probe: mir/src/lower.rs used to mark a closure's destination local Copy when THAT closure's "
        "captures were all Copy; now a local is Copy only if every closure written into it is",
    ("g6_large_elim_variable_index.lrl", "main"):
        "regression probe: MIR typing lowers `T (succ n)` (large elimination stuck at variable `n`) to `Pair[Nat, Opaque(app)]`; "
        "it diverged (M300) until stuck types were made compatible with loan-free known types",
    ("g7_fnmut_minor_reborrow.lrl", "f"):
        "kernel accepts, MIR rejects (open): the succ minor-premise closure holds `&mut m` (not Copy) and is both passed "
        "to the recursor and called (M100); its outer lambda returns a closure holding a reborrow through the captured "
        "reference, which NLL treats as dangling at that reference's StorageDead (M203). Two lowering bugs on this "
        "program (M300 nested reborrow type, M206/M200 region collision) are fixed",
    # kernel accepts, MIR rejects
    ("30_proof_closure_duplicated.lrl", "f"):
        "regression (positive control P19): a closure whose result is a proof is erased and Copy for the kernel; "
        "MIR used to lower it as a value capturing the token and rejected its second move (M100); proof-typed "
        "closures are now built without captures",
    ("30_proof_closure_duplicated_macro.lrl", "f"):
        "same as the hand-written version (proof-typed closure built without captures)",
}

results_dir_global = []

# Cause notes that follow from the kernel code alone (checks that only the kernel performs by design).
KERNEL_ONLY_NOTES = {
    "K0022": "effects are a kernel-only check (`check_effects`); MIR has no effect analysis",
    "K0023": "axiom dependencies are a kernel-only check; MIR does not track axioms",
}


def cause_note(rec):
    if rec is None:
        return None
    note = CAUSE_NOTES.get((os.path.basename(rec["file"]), rec["name"]))
    if note:
        return note
    return KERNEL_ONLY_NOTES.get(rec["kernel_admit"].get("code") or "")

NLL_CODES = {"M200", "M201", "M202", "M203", "M204", "M205", "M206", "M207"}


def load(results_dir):
    data = {}
    for backend in sorted(os.listdir(results_dir)):
        bdir = os.path.join(results_dir, backend)
        if not os.path.isdir(bdir):
            continue
        for name in sorted(os.listdir(bdir)):
            if not name.endswith(".jsonl") or name.startswith("._"):
                continue
            with open(os.path.join(bdir, name)) as fh:
                data[(backend, name[:-6])] = [json.loads(l) for l in fh if l.strip()]
    return data


def mir_codes(rec):
    m = rec.get("mir") or {}
    codes = []
    for key in ("typing_errors", "ownership_errors", "borrow_errors"):
        for e in m.get(key, []):
            if e["code"] not in codes:
                codes.append(e["code"])
    if m.get("lower_error"):
        codes.append("lowering")
    if m.get("panic"):
        codes.append("panic")
    return codes


def mir_verdict(rec):
    """'ok' | 'reject' | 'n/a' (no elaborated term) | 'panic'."""
    m = rec.get("mir")
    if m is None:
        return "n/a"
    if m.get("panic"):
        return "panic"
    return "ok" if m.get("ok") else "reject"


def mir_cell(rec):
    v = mir_verdict(rec)
    if v == "n/a":
        return "n/a (no core term)"
    if v == "ok":
        return "accepts"
    codes = mir_codes(rec)
    m = rec["mir"]
    if "lowering" in codes:
        return "rejects (lowering error: %s)" % short(m.get("lower_error"), 70)
    return "rejects " + ", ".join(codes)


def kernel_cell(rec):
    ka = rec["kernel_admit"]
    kt = rec["kernel_typing"]
    if rec["elab"]["ok"] is not True:
        return "n/a (elaboration failed)"
    if kt["ok"] is False:
        return "rejects %s (typing)" % (kt.get("code") or "?")
    if ka["ok"] is True:
        return "accepts"
    if ka["ok"] is False:
        return "rejects %s %s (%s)" % (ka.get("code") or "?", ka.get("variant") or "", ka.get("phase"))
    return "n/a"


def short(text, n=110):
    text = (text or "").replace("|", "\\|")
    return text if len(text) <= n else text[: n - 3] + "..."


def first_cli_error(rec):
    errs = rec.get("cli", {}).get("errors", [])
    if not errs:
        return None
    e = errs[0]
    return "%s %s" % (e.get("code") or "(no code)", short(e.get("msg"), 90))


def git_rev(root):
    try:
        rev = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=root, capture_output=True,
                             text=True).stdout.strip()
        # Modified tracked files, not counting results files (which reruns of the scripts rewrite).
        dirty = subprocess.run(["git", "status", "--porcelain", "--untracked-files=no", "--", ".",
                                ":!**/results_*.md", ":!**/SUMMARY.md", ":!bench/results", ":!paper"],
                               cwd=root, capture_output=True, text=True).stdout.strip()
        dirty = "\n".join(l for l in dirty.splitlines() if not l.startswith("error"))
        return rev + (" (with uncommitted changes outside results files)" if dirty else "")
    except OSError:
        return "unknown"


def provenance_line(args):
    """Header line with the SHA-256 of the binaries that produced the results."""
    tool = ("`%s`" % args.tool_sha256) if args.tool_sha256 else "not recorded"
    check_path = os.path.join(args.results, "cli_check.json")
    if os.path.exists(check_path):
        cli_name = os.path.basename(json.load(open(check_path)).get("cli", "cli"))
        cli = ("`%s` (`%s`)" % (args.cli_sha256, cli_name)) if args.cli_sha256 else \
            "not recorded (`%s`)" % cli_name
    else:
        cli = "none (the CLI cross-check was not run)"
    return ("Binaries (SHA-256): stage_matrix tool %s; CLI binary of the cross-check %s.\n" % (tool, cli))


def read_manifest(root):
    path = os.path.join(root, "case_studies", "corpus", "manifest.tsv")
    if not os.path.exists(path):
        return None, []
    rows = []
    with open(path) as fh:
        lines = [l.rstrip("\n") for l in fh if l.strip() and not l.startswith("#")]
    if not lines:
        return path, []
    header = [h.strip().lower() for h in lines[0].split("\t")]
    for line in lines[1:]:
        cols = line.split("\t")
        rows.append({header[i] if i < len(header) else str(i): c.strip() for i, c in enumerate(cols)})
    return path, rows


def expected_neg_files(root):
    """Expected-negative files of the repository's own corpus contract (lrl_corpus_expectations.rs)."""
    path = os.path.join(root, "cli", "tests", "lrl_corpus_expectations.rs")
    if not os.path.exists(path):
        return set()
    return set(re.findall(r'"(tests/[^"]+\.lrl)"', open(path).read()))


def records(data, backend, set_name, kind):
    return [r for r in data.get((backend, set_name), []) if r.get("record") == kind]


def section_selfcheck(data, out):
    out.append("## 0. Harness self-check\n")
    out.append("For every definition and top-level expression the harness predicts admission "
               "(`kernel_admit` ok AND interior-mutability gate ok AND every MIR check ok on the admitted "
               "definition) and compares it with the unmodified CLI driver replaying the same form "
               "(`cli::driver::process_code`). `inconsistent` counts records where the two differ; "
               "`crash` counts files whose run ended abnormally.\n")
    out.append("| backend prelude | set | files | file-level failures | def records | expr records | inconsistent | crash |")
    out.append("|---|---|---:|---:|---:|---:|---:|---:|")
    for (backend, set_name), recs in sorted(data.items()):
        files = [r for r in recs if r["record"] == "file"]
        bad_files = [r for r in files if r.get("status") != "ok"]
        defs = [r for r in recs if r["record"] == "def"]
        n_def = sum(1 for r in defs if r["kind"] != "expr")
        n_expr = sum(1 for r in defs if r["kind"] == "expr")
        inc = sum(1 for r in defs if not r["consistent"])
        crash = sum(1 for r in recs if r["record"] == "crash")
        out.append("| %s | %s | %d | %d | %d | %d | %d | %d |" % (
            backend, set_name, len(files), len(bad_files), n_def, n_expr, inc, crash))
    out.append("")
    incs = [(k, r) for k, recs in sorted(data.items()) for r in recs
            if r["record"] == "def" and not r["consistent"]]
    if incs:
        out.append("Inconsistent records:\n")
        for (backend, set_name), r in incs:
            out.append("- %s/%s `%s` line %s `%s`: predicted %s, CLI %s" % (
                backend, set_name, r["file"], r["line"], r["name"], r["predicted_admitted"], r["cli_admitted"]))
        out.append("")
    check_path = os.path.join(results_dir_global[0], "cli_check.json")
    if os.path.exists(check_path):
        check = json.load(open(check_path))
        out.append("Cross-check against the CLI binary (`check_against_cli.py`, dynamic prelude): every file was also run "
                   "whole with `%s run <file>`; for %d of %d files the multiset of diagnostic codes on its `Error:` lines "
                   "and its exit status (non-zero iff an error) agree with the per-form replay.\n" % (
                       os.path.basename(check["cli"]), check["same"], check["files"]))
        for d in check["diffs"]:
            out.append("- differs: `%s` exit %s, CLI %s, replay %s" % (d["file"], d["exit"], d["cli_codes"], d["replay_codes"]))
        if check["diffs"]:
            out.append("")
    else:
        out.append("The optional cross-check against a CLI binary (`STAGE_MATRIX_CLI`) was not run.\n")
    crashes = [r for recs in data.values() for r in recs if r["record"] == "crash"]
    for r in crashes:
        out.append("- crash: %s (%s): exit %s, stderr tail `%s`" % (
            r["file"], r["backend"], r["exit"], short(r.get("stderr_tail", "").strip(), 200)))
    if crashes:
        out.append("")


def corpus_rows(recs):
    """Group the validation-corpus records by file."""
    byfile = collections.OrderedDict()
    for r in recs:
        if r["record"] in ("file", "def", "form", "crash"):
            byfile.setdefault(r["file"], []).append(r)
    return byfile


def describe_file(rs):
    """(first rejecting point, kernel cell, MIR cell, mir-would-catch, rec) for one corpus file."""
    file_rec = next((r for r in rs if r["record"] == "file"), None)
    if file_rec and file_rec.get("status") != "ok":
        status = file_rec.get("status")
        stage = "expansion" if status == "expansion_error" else status
        what = "%s %s (whole file; no declaration is processed)" % (stage, file_rec.get("code") or "")
        return what, "n/a", "n/a (no core term)", "n/a (rejected before elaboration)", None
    for r in rs:
        if r["record"] == "form" and not r["cli"]["ok"]:
            errs = r["cli"]["errors"]
            code = errs[0]["code"] if errs else "?"
            return ("%s declaration `%s`: %s" % (r["kind"], r.get("name"), code), "rejects %s (declaration)" % code,
                    "n/a (not a definition)", "n/a (declaration-level check)", None)
        if r["record"] == "def" and not r["cli_admitted"]:
            if r["elab"]["ok"] is not True:
                where = "elaborator %s" % (r["elab"].get("code") or r["elab"].get("phase"))
                return where, kernel_cell(r), mir_cell(r), "n/a (no core term)", r
            if r["kernel_typing"]["ok"] is False:
                where = "kernel typing %s" % r["kernel_typing"].get("code")
            elif r["kernel_admit"]["ok"] is False:
                where = "kernel %s %s" % (r["kernel_admit"].get("code"), r["kernel_admit"].get("variant") or "")
            elif r.get("gate"):
                where = "driver gate %s" % r["gate"]
            else:
                where = "MIR " + ", ".join(mir_codes(r))
            mv = mir_verdict(r)
            if r["kernel_typing"]["ok"] is False:
                catch = "n/a (kernel typing rejects; MIR on an ill-typed term is not a verdict)"
            elif r["kernel_admit"]["ok"] is True:
                catch = "MIR only (kernel accepts)" if mv == "reject" else "-"
            else:
                catch = {"reject": "yes (%s)" % ", ".join(mir_codes(r)), "ok": "**no**",
                         "panic": "MIR panics", "n/a": "n/a"}[mv]
            return where, kernel_cell(r), mir_cell(r), catch, r
    return "accepted (nothing rejected)", "-", "-", "-", None


def corpus_classes(byfile, manifest):
    """[(class id, kind, description, [(file basename, expected stage, expected code)])] in manifest order,
    or derived from file names (NN_name.lrl + NN_name_macro.lrl; pNN_... = positive) without a manifest."""
    classes = []
    if manifest:
        for row in manifest:
            files = []
            if row.get("file"):
                files.append((row["file"], row.get("stage", ""), row.get("code", "")))
            if row.get("twin"):
                files.append((row["twin"], row.get("twin_stage", ""), row.get("twin_code", "")))
            classes.append((row.get("class", "?"), row.get("kind", "?"), row.get("description", ""), files))
        listed = {f for c in classes for (f, _, _) in c[3]}
        extra = [os.path.basename(f) for f in byfile if os.path.basename(f) not in listed]
        if extra:
            classes.append(("-", "unlisted", "files not in manifest.tsv", [(f, "", "") for f in extra]))
        return classes
    groups = collections.OrderedDict()
    for f in byfile:
        base = os.path.basename(f)
        cls = base.split("_")[0]
        groups.setdefault(cls, []).append((base, "", ""))
    for cls, files in groups.items():
        kind = "positive" if re.match(r"^p\d", cls) else "negative"
        classes.append((cls, kind, "", files))
    return classes


def section_corpus(data, backend, root, out):
    recs = data.get((backend, "corpus"))
    if not recs:
        out.append("## 1. Validation corpus\n\n`case_studies/corpus/` was not present when the script ran.\n")
        return
    manifest_path, manifest = read_manifest(root)
    byfile = corpus_rows(recs)
    by_base = {os.path.basename(f): rs for f, rs in byfile.items()}
    classes = corpus_classes(byfile, manifest)
    out.append("## 1. Validation corpus (`case_studies/corpus/`, %s prelude): defence in depth\n" % backend)
    out.append("For each file, the first rejected form and, for that definition, the verdict of every stage. "
               "The MIR column is computed on the elaborated term even when the kernel rejected it "
               "(`mir.env` = `pre_admission`), i.e. it answers: *would MIR also reject this definition if the "
               "kernel ownership check were absent?* `n/a (no core term)`: the elaborator or the macro expander "
               "rejected the program, so there is no term to lower. %s\n" % (
                   "Classes, kinds and expected stage/code are from `case_studies/corpus/manifest.tsv`."
                   if manifest else "No `manifest.tsv` was present; classes are derived from file names."))
    out.append("| class | file | expected (manifest) | first rejection (observed) | kernel | MIR on the same term | MIR would also catch it? |")
    out.append("|---|---|---|---|---|---|---|")
    buckets = collections.OrderedDict([
        ("kernel and MIR both reject", []), ("kernel rejects, MIR does not", []),
        ("MIR only (kernel accepts)", []), ("elaborator or expander only (no core term)", []),
        ("declaration-level (inductive) check", []),
        ("macro boundary at expansion (macro-only class; the hand-written analogue is accepted)", []),
        ("other", []),
    ])
    positives = []
    for cls, kind, desc, files in classes:
        if kind == "positive":
            positives.append((cls, desc, files))
            continue
        described = []
        for base, exp_stage, exp_code in files:
            rs = by_base.get(base)
            if rs is None:
                out.append("| %s | `%s` | %s | (no stage-matrix record) | | | |" % (cls, base, " ".join(x for x in (exp_stage, exp_code) if x) or "-"))
                continue
            where, kcell, mcell, catch, rec = describe_file(rs)
            described.append((base, where, catch, rec))
            out.append("| %s | `%s` | %s | %s | %s | %s | %s |" % (
                cls, base, " ".join(x for x in (exp_stage, exp_code) if x) or "-", short(where, 80), kcell,
                short(mcell, 80), catch))
        if not described:
            continue
        rejected = [i for i in described if not i[1].startswith("accepted")]
        accepted = [i for i in described if i[1].startswith("accepted")]
        title = "%s%s" % (cls, (" " + desc) if desc else "")
        if accepted and rejected and all("expansion" in i[1] for i in rejected):
            buckets["macro boundary at expansion (macro-only class; the hand-written analogue is accepted)"].append(
                "%s (`%s`: %s; `%s` accepted)" % (title, rejected[0][0], rejected[0][1].split(" (")[0], accepted[0][0]))
            continue
        base, where, catch, rec = (rejected or described)[0]
        others = sorted({i[2] for i in described if i[2] != catch})
        label = title + ("" if not others else " [other file: %s]" % ", ".join(others))
        if catch.startswith("yes"):
            buckets["kernel and MIR both reject"].append(label + ": " + catch[len("yes ("):-1])
        elif catch == "**no**":
            note = cause_note(rec)
            buckets["kernel rejects, MIR does not"].append(label + ": " + (note or "(not analysed)"))
        elif catch.startswith("MIR only"):
            buckets["MIR only (kernel accepts)"].append(label + ": " + ", ".join(mir_codes(rec)))
        elif "no core term" in catch or "before elaboration" in catch:
            buckets["elaborator or expander only (no core term)"].append(label + ": " + where)
        elif "declaration" in catch:
            buckets["declaration-level (inductive) check"].append(label + ": " + where)
        else:
            buckets["other"].append(label + ": " + where + " / " + catch)
    out.append("")
    out.append("Summary by class (first rejected file of each class; the other file agrees unless stated):\n")
    for bucket, items in buckets.items():
        if not items and bucket == "other":
            continue
        out.append("- **%s** (%d classes):" % (bucket, len(items)))
        for item in items:
            out.append("  - %s" % item)
        if not items:
            out.append("  - none")
    out.append("")

    if positives:
        out.append("Positive controls (must be accepted):\n")
        out.append("| class | file | definitions | every stage passes on every definition | CLI admits every form |")
        out.append("|---|---|---:|---|---|")
        for cls, desc, files in positives:
            for base, _, _ in files:
                rs = by_base.get(base)
                if rs is None:
                    out.append("| %s | `%s` | | (no stage-matrix record) | |" % (cls, base))
                    continue
                defs = [r for r in rs if r["record"] == "def"]
                all_pass = all(r["elab"]["ok"] and r["kernel_typing"]["ok"] and r["kernel_admit"]["ok"]
                               and mir_verdict(r) == "ok" for r in defs)
                file_ok = all(r.get("status") == "ok" for r in rs if r["record"] == "file")
                forms_ok = all(r["cli"]["ok"] for r in rs if r["record"] == "form")
                cli_all = file_ok and forms_ok and all(r["cli_admitted"] for r in defs)
                out.append("| %s | `%s` | %d | %s | %s |" % (cls, base, len(defs),
                                                           "yes" if all_pass and file_ok else "**no**",
                                                           "yes" if cli_all else "**no**"))
        out.append("")


def stage_counts(defs):
    rows = []

    def count(label, values):
        c = collections.Counter(values)
        rows.append((label, c.get("pass", 0), c.get("reject", 0), c.get("n/a", 0)))

    count("elaboration", ["pass" if r["elab"]["ok"] else "reject" for r in defs])
    count("kernel typing", ["n/a" if r["kernel_typing"]["ok"] is None else
                            ("pass" if r["kernel_typing"]["ok"] else "reject") for r in defs])
    count("kernel admission (add_definition)", ["n/a" if r["kernel_admit"]["ok"] is None else
                                                ("pass" if r["kernel_admit"]["ok"] else "reject") for r in defs])
    count("kernel ownership walk", [{"pass": "pass", "reject": "reject"}.get(r["kernel_ownership"], "n/a")
                                    for r in defs])
    count("MIR lowering", ["n/a" if (r.get("mir") or {}).get("lowered") is None else
                           ("pass" if r["mir"]["lowered"] else "reject") for r in defs])
    for key, label in (("typing_ok", "MIR typing"), ("ownership_ok", "MIR ownership"), ("borrow_ok", "MIR borrow check (NLL)")):
        count(label, ["n/a" if (r.get("mir") or {}).get(key) is None else
                      ("pass" if r["mir"][key] else "reject") for r in defs])
    count("CLI admits (replay)", ["pass" if r["cli_admitted"] else "reject" for r in defs])
    return rows


def section_programs(data, backend, sets, root, out, idx):
    present = [s for s in sets if (backend, s) in data]
    if not present:
        return
    neg_files = expected_neg_files(root)
    out.append("## %s. Program corpus (%s), %s prelude\n" % (idx, ", ".join("`%s`" % s for s in present), backend))
    recs = [r for s in present for r in data[(backend, s)]]
    files = [r for r in recs if r["record"] == "file"]
    defs = [r for r in recs if r["record"] == "def"]
    out.append("%d files (%d rejected as a whole before any declaration is processed), %d definitions and %d top-level "
               "expressions. A definition after a rejected one that refers to it fails elaboration (unbound "
               "name); such cascades are counted as elaboration rejections.\n" % (
                   len(files), sum(1 for f in files if f.get("status") != "ok"),
                   sum(1 for r in defs if r["kind"] != "expr"), sum(1 for r in defs if r["kind"] == "expr")))
    out.append("| stage | pass | reject | not computed |")
    out.append("|---|---:|---:|---:|")
    for label, p, rj, na in stage_counts(defs):
        out.append("| %s | %d | %d | %d |" % (label, p, rj, na))
    out.append("")

    def is_neg(path):
        return path in neg_files or "/neg/" in path

    def mark(path):
        if is_neg(path):
            return " (expected negative)"
        if "/backend_conformance/" in path:
            return " (conformance case: written for tests/backend_conformance/conformance_prelude.inc, not the standard prelude)"
        return ""

    bad_files = [f for f in files if f.get("status") != "ok"]
    if bad_files:
        out.append("Files rejected before declaration processing:\n")
        for f in bad_files:
            out.append("- `%s`%s: %s %s `%s`" % (f["file"], mark(f["file"]), f.get("status"), f.get("code") or "", short(f.get("msg"), 120)))
        out.append("")

    def show(rec):
        note = cause_note(rec)
        return "`%s`:%s `%s`%s" % (rec["file"], rec["line"], rec["name"], mark(rec["file"])), note

    form_fail = [r for r in recs if r["record"] == "form" and not r["cli"]["ok"]]
    if form_fail:
        out.append("Rejected non-definition forms (inductive/axiom/... declarations; later definitions using them fail "
                   "elaboration):\n")
        for r in form_fail:
            errs = r["cli"]["errors"]
            first = "%s %s" % (errs[0].get("code") or "(no code)", short(errs[0]["msg"], 110)) if errs else "?"
            out.append("- `%s`:%s %s `%s`%s: %s" % (r["file"], r["line"], r["kind"], r.get("name"), mark(r["file"]), first))
        out.append("")

    ka_mr = [r for r in defs if r["kernel_admit"]["ok"] is True and mir_verdict(r) in ("reject", "panic")]
    kr_ma = [r for r in defs if r["kernel_admit"]["ok"] is False and r["kernel_typing"]["ok"] is True
             and mir_verdict(r) == "ok"]
    kt_fail = [r for r in defs if r["kernel_typing"]["ok"] is False]
    out.append("**Kernel accepts, MIR rejects** (%d definitions), grouped by MIR codes:\n" % len(ka_mr))
    groups = collections.OrderedDict()
    for r in ka_mr:
        codes = mir_codes(r)
        if codes and all(c in NLL_CODES for c in codes):
            key = "loan errors only (%s): the kernel has no loan tracking (T2 FINAL walk, section 9); NLL is MIR-only" % ", ".join(sorted(set(codes)))
        else:
            key = "MIR " + ", ".join(codes)
        groups.setdefault(key, []).append(r)
    for key, rs in groups.items():
        out.append("- %s:" % key)
        for r in rs:
            where, note = show(r)
            errs = [e for k in ("typing_errors", "ownership_errors", "borrow_errors") for e in r["mir"].get(k, [])]
            first = "%s %s: %s" % (errs[0]["body"], errs[0]["code"], short(errs[0]["msg"], 100)) if errs else short(r["mir"].get("lower_error"), 100)
            out.append("  - %s — %s%s" % (where, first, ("; cause: " + note) if note else ""))
    if not ka_mr:
        out.append("- none")
    out.append("")
    out.append("**Kernel rejects, MIR accepts** (%d definitions), grouped by kernel code:\n" % len(kr_ma))
    groups = collections.OrderedDict()
    for r in kr_ma:
        groups.setdefault("%s %s (%s)" % (r["kernel_admit"]["code"], r["kernel_admit"]["variant"], r["kernel_admit"]["phase"]), []).append(r)
    for key, rs in groups.items():
        out.append("- %s:" % key)
        for r in rs:
            where, note = show(r)
            out.append("  - %s — %s; cause: %s" % (where, short(r["kernel_admit"]["msg"], 100), note or "(not analysed)"))
    if not kr_ma:
        out.append("- none")
    out.append("")
    if kt_fail:
        out.append("**Rejected by kernel typing** (MIR result on an ill-typed term not interpreted): %d\n" % len(kt_fail))
        for r in kt_fail:
            where, _ = show(r)
            out.append("- %s: %s `%s`" % (where, r["kernel_typing"].get("code"), short(r["kernel_typing"].get("msg"), 100)))
        out.append("")
    both = [r for r in defs if r["kernel_admit"]["ok"] is False and r["kernel_typing"]["ok"] is True
            and mir_verdict(r) == "reject"]
    out.append("**Kernel and MIR both reject** (%d definitions):\n" % len(both))
    for r in both:
        where, _ = show(r)
        out.append("- %s — kernel %s %s; MIR %s" % (where, r["kernel_admit"]["code"], r["kernel_admit"]["variant"], ", ".join(mir_codes(r))))
    if not both:
        out.append("- none")
    out.append("")
    elab_fail = [r for r in defs if r["elab"]["ok"] is False]
    out.append("**Rejected by the elaborator** (no core term; kernel and MIR not computed): %d\n" % len(elab_fail))
    for r in elab_fail:
        where, _ = show(r)
        out.append("- %s: %s %s `%s`" % (where, r["elab"].get("phase"), r["elab"].get("code") or "", short(r["elab"].get("msg"), 100)))
    out.append("")


def section_gaps(data, out, idx):
    recs = data.get(("dynamic", "mir_gaps"))
    if not recs:
        return
    out.append("## %s. MIR-independence probes (`case_studies/tools/stage_matrix/gaps/`, dynamic prelude)\n" % idx)
    out.append("Minimal programs isolating each mechanism by which MIR, run on a kernel-rejected definition, accepted it "
               "(or rejected a kernel-accepted one) when the probe was written. The kernel verdict decides admission, so the "
               "full pipeline rejects every kernel-rejected program; these rows bound the claim that MIR re-checks ownership "
               "independently. `diverges` is computed from this run (a fixed mechanism shows `no`).\n")
    out.append("| file | definition | kernel | MIR on the same term | diverges | CLI | mechanism |")
    out.append("|---|---|---|---|---|---|---|")
    targets = {(f, d) for (f, d) in CAUSE_NOTES if re.match(r"^g\d+_", f)}
    for r in recs:
        if r["record"] != "def":
            continue
        key = (os.path.basename(r["file"]), r["name"])
        diverges = (r["kernel_admit"]["ok"] is False and mir_verdict(r) == "ok") or \
                   (r["kernel_admit"]["ok"] is True and mir_verdict(r) != "ok")
        if key not in targets and not diverges:
            continue
        note = cause_note(r) or "(not analysed)"
        cli = first_cli_error(r) or "admitted"
        out.append("| `%s` | `%s` | %s | %s | %s | %s | %s |" % (
            key[0], r["name"], kernel_cell(r), mir_cell(r), "**yes**" if diverges else "no", short(cli, 60), note))
    out.append("")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--results", required=True)
    ap.add_argument("--root", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--command", default="case_studies/tools/run_stage_matrix.sh")
    ap.add_argument("--tool-sha256", default=None,
                    help="SHA-256 of the stage_matrix tool binary that produced the JSON lines")
    ap.add_argument("--cli-sha256", default=None,
                    help="SHA-256 of the CLI binary used for the cross-check (check_against_cli.py)")
    args = ap.parse_args()
    data = load(args.results)
    results_dir_global.append(args.results)
    backends = sorted({b for (b, _) in data})
    out = []
    out.append("# Stage matrix: per-definition verdicts of every compiler stage\n")
    out.append("Generated by `%s` on %s from the JSON lines in `%s`; repository at %s. "
               "Do not edit by hand: re-run the script. Tool and method: `case_studies/tools/stage_matrix/README.md`.\n" % (
                   args.command, datetime.datetime.now().strftime("%Y-%m-%d %H:%M"),
                   os.path.relpath(args.results, args.root), git_rev(args.root)))
    out.append(provenance_line(args))
    out.append("Stages per definition: **elaboration** (frontend), **kernel typing** (`checker::infer`/`check`), "
               "**kernel admission** (`Env::add_definition` on a cloned environment: typing, the kernel ownership walk, "
               "capture modes, effects, termination, axioms; the *kernel ownership walk* verdict is derived from the phase "
               "that failed), **MIR lowering**, **MIR typing**, **MIR ownership** (moves) and **MIR borrow check** (NLL), "
               "the last three on the definition body and every derived closure body. MIR is computed even when the kernel "
               "rejects (on the elaborated term, in the environment before admission).\n")
    section_selfcheck(data, out)
    idx = 1
    for b in backends:
        if (b, "corpus") in data:
            section_corpus(data, b, args.root, out)
            break
    else:
        section_corpus(data, backends[0] if backends else "dynamic", args.root, out)
    idx = 2
    for b in backends:
        section_programs(data, b, ["tests", "code_examples", "case_studies"], args.root, out, idx)
        idx += 1
    section_gaps(data, out, idx)
    out.append("## Audit note\n")
    out.append("Every count, code and verdict above is computed by `summarize.py` from the JSON lines written by "
               "`stage_matrix` in the run named in the header (no number is entered by hand). The only hand-written text "
               "is the cause notes (`CAUSE_NOTES`, `KERNEL_ONLY_NOTES` in `summarize.py`), established by reading the MIR "
               "(`stage_matrix --dump-mir`) and the cited source files; see `case_studies/tools/stage_matrix/README.md`.")
    with open(args.out, "w") as fh:
        fh.write("\n".join(out).rstrip() + "\n")


if __name__ == "__main__":
    main()
