#!/usr/bin/env python3
"""Check every repository reference cited in the paper's LaTeX sources.

Run from the repository root:

    python3 paper/jot_r1/scripts/check_references.py [--cli <path to the lrl/cli binary>]

The script extracts the contents of \\texttt{...} and \\lstinline|...| from paper/jot_r1/sections/*.tex
and classifies each token:

- file paths (containing '/' or ending in a known extension) must exist in the repository;
- diagnostic codes (F/K/M followed by digits) must occur in docs/diagnostic_codes.md or the code;
- command-line flags (starting with --) must occur in the CLI's --help output;
- identifiers (snake_case or CamelCase words) must occur in the repository's sources.

LRL source snippets and other tokens are listed as 'not checked'. The report is printed as Markdown.
"""
import argparse
import os
import re
import subprocess
import sys

ROOT = os.getcwd()
SECTIONS = os.path.join(ROOT, "paper/jot_r1/sections")
SOURCE_DIRS = ["kernel", "frontend", "mir", "cli", "codegen", "stdlib", "mechanization/src", "case_studies",
               "bench", "docs", "tests", "code_examples"]


def tokens():
    out = []
    for name in sorted(os.listdir(SECTIONS)):
        if not name.endswith(".tex") or name.startswith("._"):
            continue
        text = open(os.path.join(SECTIONS, name)).read()
        text = "\n".join(l for l in text.split("\n") if not l.lstrip().startswith("%"))
        for m in re.finditer(r"\\texttt\{((?:[^{}]|\{[^{}]*\})*)\}", text):
            out.append((name, "texttt", m.group(1)))
        for m in re.finditer(r"\\lstinline\|([^|]*)\|", text):
            out.append((name, "lstinline", m.group(1)))
    return out


def clean(tok):
    t = tok.replace("\\_", "_").replace("-{}-", "--").replace("\\-", "")
    t = re.sub(r"\\allowbreak\s*", "", t)
    t = re.sub(r"\\[a-zA-Z]+\s*", "", t)
    return re.sub(r"\s+", " ", t.replace("{", "").replace("}", "")).strip()


def grep(word):
    paths = [p for p in SOURCE_DIRS if os.path.exists(os.path.join(ROOT, p))]
    r = subprocess.run(["grep", "-rIl", "--exclude=._*", "-F", word] + paths, cwd=ROOT,
                       capture_output=True, text=True)
    files = [l for l in r.stdout.split("\n") if l and "/._" not in l]
    return files


# Tokens that name syntax of other languages or general concepts, not repository facts.
EXTERNAL = {"&self": "Rust receiver syntax", "&mutself": "Rust receiver syntax", "&mut self": "Rust receiver syntax",
            "self": "Rust receiver syntax", "Fn": "Rust trait name", "FnMut": "Rust trait name",
            "FnOnce": "Rust trait name", "Copy": "Rust trait name / paper term", "move": "Rust keyword",
            "Vector": "Lean 4 library type", "Vect": "Idris 2 library type", "Data.Linear": "Idris 2 library module",
            "linear": "Idris 2 package", "contrib": "Idris 2 package", "believe_me": "Idris 2 primitive",
            "macro_rules!": "Rust macro system", "$crate::": "Rust macro path", "syntax-parse": "Racket library",
            "rustc": "Rust compiler", "rustc -O": "Rust compiler flag", "sorry": "Lean keyword", "admit": "Lean keyword"}
COMMANDS = {"lrl", "cargo", "rustc", "lake", "python3", "git"}
LRL_DIRS = ["stdlib", "tests", "code_examples", "case_studies"]


def grep_dirs(word, dirs, whole=False):
    paths = [p for p in dirs if os.path.exists(os.path.join(ROOT, p))]
    flags = ["-rIl", "--exclude=._*", "-F"] + (["-w"] if whole else [])
    r = subprocess.run(["grep"] + flags + [word] + paths, cwd=ROOT, capture_output=True, text=True)
    return [l for l in r.stdout.split("\n") if l and "/._" not in l]


def check_command(t, help_text, cli):
    words = t.split(" ")
    if words[0] not in COMMANDS:
        if t in EXTERNAL:
            return "external", EXTERNAL[t]
        # an LRL snippet containing spaces: it must occur in some LRL file (spacing normalised)
        return check_word(t, "lstinline")
    bad = [w for w in words if w.startswith("--") and cli and w.split("=")[0] not in help_text]
    if words[0] == "lrl" and bad:
        return "MISSING", "unknown flags " + " ".join(bad)
    return "command", f"program {words[0]}" + ("; flags in lrl --help" if words[0] == "lrl" else "")


def check_word(t, kind):
    if t in EXTERNAL:
        return "external", EXTERNAL[t]
    # LRL syntax and names: must occur in an LRL source file, or in the Rust sources/docs.
    norm = re.sub(r"\s+", " ", t)
    hits = grep_dirs(norm, LRL_DIRS) or grep_dirs(norm.replace("(", "( ").replace(")", " )"), LRL_DIRS)
    if hits:
        return "ok", "LRL source: " + hits[0]
    hits = grep_dirs(norm, SOURCE_DIRS, whole=bool(re.fullmatch(r"\w+", norm)))
    if hits:
        return "ok", "source: " + hits[0]
    return "unverified", "no exact occurrence (check by hand)"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cli", default=None)
    args = ap.parse_args()
    help_text = ""
    if args.cli:
        for sub in [[], ["run"], ["compile"], ["build"]]:
            r = subprocess.run([args.cli] + sub + ["--help"], cwd=ROOT, capture_output=True, text=True)
            help_text += r.stdout + r.stderr
    seen = {}
    for f, kind, raw in tokens():
        t = clean(raw)
        if not t or t in seen:
            continue
        status, evidence = "not checked", ""
        if " " in t:
            first = t.split(" ")[0]
            if t.startswith("--"):
                flag = first
                status = ("ok" if args.cli and flag in help_text else ("MISSING" if args.cli else "not checked"))
                evidence = "lrl --help (flag with value)"
            else:
                status, evidence = check_command(t, help_text, args.cli)
        elif re.fullmatch(r"[FKM]\d{3,4}(xx)?", t) or re.fullmatch(r"[FKM]\d{2}xx", t):
            if t.endswith("xx"):
                status, evidence = "prefix", "code family"
            else:
                hits = grep(t)
                status = "ok" if hits else "MISSING"
                evidence = ", ".join(hits[:2])
        elif t.startswith("--") or t.startswith("-O"):
            flag = t.split("=")[0]
            if flag == "-O":
                status, evidence = "rustc flag", "rustc -O"
            elif args.cli:
                status = "ok" if flag in help_text else "MISSING"
                evidence = "lrl --help"
        elif ("/" in t or re.search(r"\.(rs|lrl|lean|py|sh|md|tsv|csv|toml)$", t)) and not t.startswith("("):
            path = t.rstrip("/")
            if "*" in path:
                import glob
                hits = glob.glob(os.path.join(ROOT, path)) or glob.glob(os.path.join(ROOT, "**", path), recursive=True)
                status = "ok" if hits else "MISSING"
                evidence = f"{len(hits)} matches"
            elif os.path.exists(os.path.join(ROOT, path)):
                status, evidence = "ok", "exists"
            else:
                # a bare file or directory name mentioned in the context of a path cited nearby
                dirs = [p for p in SOURCE_DIRS if os.path.exists(os.path.join(ROOT, p))]
                r = subprocess.run(["find"] + dirs + ["-path", f"*/{path}", "-not", "-name", "._*", "-print"],
                                   cwd=ROOT, capture_output=True, text=True)
                hits = [l for l in r.stdout.split("\n") if l]
                status = "ok" if hits else "MISSING"
                evidence = (f"found as {hits[0]}" + (f" (+{len(hits)-1})" if len(hits) > 1 else "")) if hits else "no such path"
        elif re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(::[A-Za-z_][A-Za-z0-9_]*)*", t) and (
                "_" in t or re.search(r"[a-z][A-Z]", t)):
            word = t.split("::")[-1]
            hits = grep(word)
            status = "ok" if hits else "MISSING"
            evidence = ", ".join(hits[:2])
        if status == "not checked":
            status, evidence = check_word(t, kind)
        seen[t] = (f, kind, status, evidence)
    print("| token | first file | kind | status | evidence |\n|---|---|---|---|---|")
    missing = 0
    from collections import Counter
    counts = Counter(v[2] for v in seen.values())
    for t, (f, kind, status, evidence) in seen.items():
        if status == "MISSING":
            missing += 1
        print(f"| `{t}` | {f} | {kind} | {status} | {evidence} |")
    print(f"\n{len(seen)} distinct tokens; " + ", ".join(f"{k}: {v}" for k, v in sorted(counts.items())) + ".")
    return 1 if missing else 0


if __name__ == "__main__":
    sys.exit(main())
