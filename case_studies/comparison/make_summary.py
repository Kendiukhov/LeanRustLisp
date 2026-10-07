#!/usr/bin/env python3
"""Write case_studies/comparison/SUMMARY.md from the results files of the comparison.

Usage:  python3 case_studies/comparison/make_summary.py

The table is derived ONLY from the generated results files (no other input):
  results_lean_idris.md   (run_lean_idris.sh: Lean 4, Idris 2)
  results_rust_racket.md  (run_rust_racket.sh: rustc and the Racket family)
  results_lrl.md          (run_lrl.sh: LRL, typed and dynamic backends)
Each cell summarises the rows of one property (Q1..Q12) and one language: whether a correct
program using the feature was accepted, and how the violations (negative programs) were
caught, with the positive program(s) as pointers.
"""

import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

PROPERTIES = {}  # Q -> property text (from the files)


def table_rows(path, header_start):
    """Rows (lists of cells) of the first markdown table whose header starts with header_start."""
    rows, header, inside = [], None, False
    for line in open(path, encoding="utf-8"):
        line = line.rstrip("\n")
        if not inside:
            if line.startswith(header_start):
                header = [c.strip() for c in line.strip("|").split("|")]
                inside = True
            continue
        if line.startswith("|---"):
            continue
        if not line.startswith("|"):
            break
        cells = [c.strip() for c in re.split(r"(?<!\\)\|", line.strip().strip("|"))]
        rows.append(dict(zip(header, cells)))
    return rows


def program_name(cell):
    m = re.search(r"`([^`]+)`", cell)
    text = m.group(1) if m else cell
    return text


def base_program(cell):
    """The file of a program cell, without variant suffixes such as `(--cfg x)` or `[IR: ...]`."""
    name = program_name(cell)
    name = re.sub(r"\s*\[.*\]$", "", name)
    name = re.sub(r"\s*\(.*\)$", "", name)
    return name


def collect():
    data = {}  # (Q, column) -> list of (dialect, kind, observed, program)

    def add(q, column, dialect, kind, observed, program):
        data.setdefault((q, column), []).append((dialect, kind, observed, program))

    for r in table_rows(os.path.join(HERE, "results_lean_idris.md"), "| Q | Property | Lang"):
        q = r["Q"]
        PROPERTIES.setdefault(q, r["Property"])
        column = {"lean": "Lean 4", "idris2": "Idris 2"}.get(r["Lang"], r["Lang"])
        add(q, column, column, r["Kind"], r["Observed"], r["Program (variant)"])

    for r in table_rows(os.path.join(HERE, "results_rust_racket.md"), "| Q | Dialect | Program"):
        q = r["Q"]
        column = "Rust" if r["Dialect"] == "rustc" else "Racket family"
        add(q, column, r["Dialect"], r["Kind"], r["Observed"], r["Program (variant)"])

    for r in table_rows(os.path.join(HERE, "results_lrl.md"), "| Q | Dialect | Program"):
        q = r["Q"]
        add(q, "LRL", r["Dialect"], r["Kind"], r["Observed"], r["Program (variant)"])

    for r in table_rows(os.path.join(HERE, "results_rust_racket.md"), "| Q | Property | Dialect"):
        PROPERTIES.setdefault(r["Q"], r["Property"])
    for r in table_rows(os.path.join(HERE, "results_lrl.md"), "| Q | Property | Dialect"):
        PROPERTIES.setdefault(r["Q"], r["Property"])
    return data


def is_evidence(row):
    """Rows that quote intermediate or generated code (`[IR: ...]`, `[--dumpcases: ...]`,
    `[generated Rust: ...]`, ...) of a program that has its own build row.

    A NEGATIVE row is never evidence, even with a bracketed variant: it is a violation checked
    under another build command (e.g. Rust Q1 `[--emit=metadata]`, a check-only build that does
    not detect the violation) and counts among the violations of its cell."""
    return "[" in program_name(row[3]) and row[1] != "negative"


# Observed outcomes of `limit` evidence rows that state what a language cannot express at all
# (written by run_lrl.sh from the generated code or the stdlib); shown first in the cell.
LIMIT_OUTCOMES = {
    "NOT_IN_PLACE": "no in-place update: the generated code allocates new cells",
    "NO_OPERATION_ON_REF": "no operation reads or writes through a reference (references can only be created and passed)",
}


def verdict(rows):
    """Short observed verdict for one dialect's rows."""
    evidence = [r for r in rows if is_evidence(r)]
    rows = [r for r in rows if not is_evidence(r)]
    pos = [r for r in rows if r[1] == "positive"]
    neg = [r for r in rows if r[1] == "negative"]
    lim = [r for r in rows if r[1] == "limit"]
    parts = []
    for outcome in sorted({r[2] for r in evidence if r[1] == "limit" and r[2] in LIMIT_OUTCOMES}):
        parts.append("not expressible: " + LIMIT_OUTCOMES[outcome])
    if pos:
        ok = [r for r in pos if r[2] == "ACCEPT"]
        if not ok:
            failed = sorted({r[2] for r in pos})
            if failed == ["BACKEND_ERROR"]:
                parts.append("checks pass, code generation fails")
            else:
                parts.append("not expressible (correct program rejected)")
        elif len(ok) < len(pos):
            parts.append("%d of %d correct programs not accepted" % (len(pos) - len(ok), len(pos)))
    if neg:
        caught_static = [r for r in neg if r[2] == "COMPILE_ERROR"]
        caught_run = [r for r in neg if r[2] == "RUNTIME_ERROR"]
        missed = [r for r in neg if r[2] in ("ACCEPT", "BACKEND_ERROR")]
        if len(caught_static) == len(neg):
            parts.append("static (compile error), %d of %d violations" % (len(neg), len(neg)))
        elif not missed:
            parts.append(
                "run time only, %d of %d violations" % (len(caught_run), len(neg)) if not caught_static else
                "static %d, run time %d of %d violations" % (len(caught_static), len(caught_run), len(neg))
            )
        else:
            detail = []
            if caught_static:
                detail.append("static %d" % len(caught_static))
            if caught_run:
                detail.append("run time %d" % len(caught_run))
            detail.append("not detected %d" % len(missed))
            parts.append("%s of %d violations" % (", ".join(detail), len(neg)))
    if lim:
        outcomes = sorted({r[2].lower().replace("_", " ") for r in lim})
        parts.append("limit probe: " + "/".join(outcomes))
    if not parts:
        if pos:
            parts.append("accepted (no violating program)")
        else:
            parts.append("no program")
    pointers = sorted({base_program(r[3]) for r in (pos or lim or neg)})
    text = "; ".join(parts) + " (" + ", ".join("`%s`" % p for p in pointers) + ")"
    if evidence:
        text += "; code excerpts: " + ", ".join("`%s`" % program_name(r[3]) for r in evidence)
    return text


def cell(rows, column):
    if not rows:
        return "no program"
    dialects = []
    for r in rows:
        if r[0] not in dialects:
            dialects.append(r[0])
    if column in ("Racket family", "LRL") or len(dialects) > 1:
        texts = []
        for d in dialects:
            v = verdict([r for r in rows if r[0] == d])
            texts.append("%s: %s" % (d, v))
        return "<br>".join(texts)
    return verdict(rows)


def main():
    data = collect()
    columns = ["Lean 4", "Idris 2", "Rust", "Racket family", "LRL"]
    qs = sorted(PROPERTIES, key=lambda q: int(q[1:]))
    out = []
    out.append("# Comparison summary: Lean 4, Idris 2, Rust, the Racket family and LRL")
    out.append("")
    out.append("Generated by `python3 case_studies/comparison/make_summary.py` from the three results files")
    out.append("(`results_lean_idris.md`, `results_rust_racket.md`, `results_lrl.md`); do not edit by hand.")
    out.append("Each cell is derived only from the rows of those files for that property and language:")
    out.append("")
    out.append("- *static (compile error), n of n violations*: every negative program (a violation of the property) was")
    out.append("  rejected before running; n is the number of negative programs, which differs between languages;")
    out.append("- *run time only*: violations were caught only when the program ran;")
    out.append("- *not detected*: a violation compiled and ran; *static k, run time j, not detected m of n violations*")
    out.append("  gives the counts when the negative programs had different outcomes;")
    out.append("- *not expressible*: no correct (positive) program using the feature was accepted, or (LRL) an evidence row")
    out.append("  shows that the feature does not exist (no in-place update; no operation on references);")
    out.append("- *k of n correct programs not accepted*: some, but not all, positive programs were rejected (or failed);")
    out.append("- *checks pass, code generation fails*: LRL's checks accepted the positive program but rustc rejected the")
    out.append("  generated Rust (a code-generator limitation);")
    out.append("- *limit probe*: programs that probe whether the tool can express or enforce the property at all")
    out.append("  (\"limit\" rows of the results files), with their observed outcome;")
    out.append("- the files in parentheses are the positive programs (or the probes / negatives when there is no positive one);")
    out.append("  *code excerpts* point to the rows of the results files that quote the compiler's intermediate or generated")
    out.append("  code for the property (e.g. whether an update is done in place, or whether a proof is passed at run time);")
    out.append("  a negative row with a bracketed build variant (Rust Q1 `[--emit=metadata]`, a check-only build) is not an")
    out.append("  excerpt: it is counted among the violations.")
    out.append("")
    out.append("Racket family dialects: Racket = `#lang racket/base`; Typed Racket; Typed Racket + refinements;")
    out.append("Cur (dependent types via Turnstile+ macros); Turnstile lin (the linear-types example language).")
    out.append("LRL dialects: the typed and the dynamic code generator (both run the same checks).")
    out.append("")
    out.append("| Q | Property | " + " | ".join(columns) + " |")
    out.append("|---|---|" + "---|" * len(columns))
    for q in qs:
        cells = [cell(data.get((q, c), []), c) for c in columns]
        out.append("| %s | %s | %s |" % (q, PROPERTIES[q], " | ".join(cells)))
    out.append("")
    out.append("## Audit note")
    out.append("")
    out.append("Every cell is computed by `make_summary.py` from the result rows of the three files named above; the")
    out.append("header lines of each results file record the tool versions, the date and the command that produced it.")
    out.append("No verdict is entered by hand. Rerun the three `run_*.sh` scripts, then this script, to refresh the table.")
    out.append("")
    path = os.path.join(HERE, "SUMMARY.md")
    open(path, "w", encoding="utf-8").write("\n".join(out))
    print("wrote %s (%d rows)" % (path, len(qs)))


if __name__ == "__main__":
    sys.exit(main())
