#!/usr/bin/env python3
"""Stress-test backend compile+run with generated semantically valid LRL programs.

Phase F goals:
- generate valid programs,
- compile with selected backend (`auto`/`typed`/`dynamic`),
- run produced binaries,
- classify failures and fallback reason-codes,
- optionally promote recurring failures into regression files.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable, Dict, List, Optional, Sequence, Tuple


RE_REASON = re.compile(r"TB\d{3}")
RE_ANSI = re.compile(r"\x1b\[[0-9;]*m")


@dataclass
class CaseResult:
    index: int
    template: str
    source_path: Path
    compile_ok: bool
    run_ok: bool
    backend: str
    fallback_codes: List[str]
    compile_exit: int
    run_exit: int
    compile_stdout: str
    compile_stderr: str
    run_stdout: str
    run_stderr: str
    failure_fingerprint: Optional[str]


def now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def nat_expr(value: int) -> str:
    expr = "zero"
    for _ in range(max(0, value)):
        expr = f"(succ {expr})"
    return expr


def bool_expr(value: bool) -> str:
    return "true" if value else "false"


def template_nat_identity(rng: random.Random, idx: int) -> str:
    return f"""
(def entry Nat
  {nat_expr(rng.randint(0, 6))})
""".strip()


def template_nat_pred(rng: random.Random, idx: int) -> str:
    n = rng.randint(1, 6)
    return f"""
(def pred_{idx} (pi n Nat Nat)
  (lam n Nat
    (match n Nat
      (case (zero) zero)
      (case (succ x) x))))

(def entry Nat
  (pred_{idx} {nat_expr(n)}))
""".strip()


def template_nat_add_const(rng: random.Random, idx: int) -> str:
    left = rng.randint(0, 5)
    right = rng.randint(0, 5)
    return f"""
(def add_{idx} (pi n Nat (pi m Nat Nat))
  (lam n Nat
    (lam m Nat
      (match n Nat
        (case (zero) m)
        (case (succ x ih) (succ ih))))))

(def entry Nat
  ((add_{idx} {nat_expr(left)}) {nat_expr(right)}))
""".strip()


def template_nat_double(rng: random.Random, idx: int) -> str:
    val = rng.randint(0, 4)
    return f"""
(def add_{idx} (pi n Nat (pi m Nat Nat))
  (lam n Nat
    (lam m Nat
      (match n Nat
        (case (zero) m)
        (case (succ x ih) (succ ih))))))

(def double_{idx} (pi n Nat Nat)
  (lam n Nat
    ((add_{idx} n) n)))

(def entry Nat
  (double_{idx} {nat_expr(val)}))
""".strip()


def template_bool_not(rng: random.Random, idx: int) -> str:
    b = rng.choice([True, False])
    return f"""
(def not_{idx} (pi b Bool Bool)
  (lam b Bool
    (match b Bool
      (case (true) false)
      (case (false) true))))

(def entry Bool
  (not_{idx} {bool_expr(b)}))
""".strip()


def template_bool_and(rng: random.Random, idx: int) -> str:
    a = rng.choice([True, False])
    b = rng.choice([True, False])
    return f"""
(def and_{idx} (pi a Bool (pi b Bool Bool))
  (lam a Bool
    (lam b Bool
      (match a Bool
        (case (true) b)
        (case (false) false)))))

(def entry Bool
  ((and_{idx} {bool_expr(a)}) {bool_expr(b)}))
""".strip()


def template_bool_choose_nat(rng: random.Random, idx: int) -> str:
    b = rng.choice([True, False])
    t = rng.randint(0, 4)
    f = rng.randint(0, 4)
    return f"""
(def choose_nat_{idx} (pi b Bool (pi t Nat (pi f Nat Nat)))
  (lam b Bool
    (lam t Nat
      (lam f Nat
        (match b Nat
          (case (true) t)
          (case (false) f))))))

(def entry Nat
  (((choose_nat_{idx} {bool_expr(b)}) {nat_expr(t)}) {nat_expr(f)}))
""".strip()


def template_user_pair(rng: random.Random, idx: int) -> str:
    a = rng.randint(0, 6)
    b = rng.randint(0, 6)
    return f"""
(inductive copy PairNat_{idx} (sort 1)
  (ctor mk_pair_{idx} (pi fst Nat (pi snd Nat (PairNat_{idx})))))

(def second_{idx} (pi p PairNat_{idx} Nat)
  (lam p PairNat_{idx}
    (match p Nat
      (case (mk_pair_{idx} x y) y))))

(def entry Nat
  (second_{idx} ((mk_pair_{idx} {nat_expr(a)}) {nat_expr(b)})))
""".strip()


def template_user_maybe_nested(rng: random.Random, idx: int) -> str:
    payload = rng.randint(0, 4)
    outer_is_some = rng.choice([True, False])
    inner_is_some = rng.choice([True, False])
    inner_val = (
        f"(some_nat_{idx} {nat_expr(payload)})"
        if inner_is_some
        else f"none_nat_{idx}"
    )
    outer_val = (
        f"(some_maybe_{idx} {inner_val})" if outer_is_some else f"none_maybe_{idx}"
    )
    return f"""
(inductive copy MaybeNat_{idx} (sort 1)
  (ctor none_nat_{idx} MaybeNat_{idx})
  (ctor some_nat_{idx} (pi n Nat MaybeNat_{idx})))

(inductive copy MaybeMaybeNat_{idx} (sort 1)
  (ctor none_maybe_{idx} MaybeMaybeNat_{idx})
  (ctor some_maybe_{idx} (pi m MaybeNat_{idx} MaybeMaybeNat_{idx})))

(def flatten_{idx} (pi mm MaybeMaybeNat_{idx} Nat)
  (lam mm MaybeMaybeNat_{idx}
    (match mm Nat
      (case (none_maybe_{idx}) zero)
      (case (some_maybe_{idx} m)
        (match m Nat
          (case (none_nat_{idx}) zero)
          (case (some_nat_{idx} n) n))))))

(def entry Nat
  (flatten_{idx} {outer_val}))
""".strip()


def template_user_three_ctor(rng: random.Random, idx: int) -> str:
    choose = rng.randint(0, 2)
    a = nat_expr(rng.randint(0, 3))
    b = nat_expr(rng.randint(0, 3))
    c = nat_expr(rng.randint(0, 3))
    if choose == 0:
        sample = f"(red_{idx} {a})"
    elif choose == 1:
        sample = f"(green_{idx} {b})"
    else:
        sample = f"(blue_{idx} {c})"

    return f"""
(inductive copy RGBNat_{idx} (sort 1)
  (ctor red_{idx} (pi n Nat RGBNat_{idx}))
  (ctor green_{idx} (pi n Nat RGBNat_{idx}))
  (ctor blue_{idx} (pi n Nat RGBNat_{idx})))

(def to_nat_{idx} (pi c RGBNat_{idx} Nat)
  (lam c RGBNat_{idx}
    (match c Nat
      (case (red_{idx} n) n)
      (case (green_{idx} n) n)
      (case (blue_{idx} n) n))))

(def entry Nat
  (to_nat_{idx} {sample}))
""".strip()


def template_function_chain(rng: random.Random, idx: int) -> str:
    base = rng.randint(0, 4)
    return f"""
(def inc_{idx} (pi n Nat Nat)
  (lam n Nat (succ n)))

(def twice_{idx} (pi x Nat Nat)
  (lam x Nat
    (inc_{idx} (inc_{idx} x))))

(def entry Nat
  (twice_{idx} {nat_expr(base)}))
""".strip()


def template_let_shadow_chain(rng: random.Random, idx: int) -> str:
    a = nat_expr(rng.randint(0, 3))
    return f"""
(def entry Nat
  (let x Nat {a}
    (let x Nat (succ x)
      (let y Nat (succ x)
        y))))
""".strip()


def template_bool_match_to_bool(rng: random.Random, idx: int) -> str:
    b = rng.choice([True, False])
    return f"""
(def flip_if_{idx} (pi b Bool (pi c Bool Bool))
  (lam b Bool
    (lam c Bool
      (match b Bool
        (case (true) c)
        (case (false) (match c Bool
                         (case (true) false)
                         (case (false) true)))))))

(def entry Bool
  ((flip_if_{idx} {bool_expr(b)}) true))
""".strip()


TemplateFn = Callable[[random.Random, int], str]
TEMPLATES: Sequence[Tuple[str, TemplateFn]] = [
    ("nat_identity", template_nat_identity),
    ("nat_pred", template_nat_pred),
    ("nat_add_const", template_nat_add_const),
    ("nat_double", template_nat_double),
    ("bool_not", template_bool_not),
    ("bool_and", template_bool_and),
    ("bool_choose_nat", template_bool_choose_nat),
    ("user_pair", template_user_pair),
    ("user_maybe_nested", template_user_maybe_nested),
    ("user_three_ctor", template_user_three_ctor),
    ("function_chain", template_function_chain),
    ("let_shadow_chain", template_let_shadow_chain),
    ("bool_match_to_bool", template_bool_match_to_bool),
]


def run_cmd(args: Sequence[str], cwd: Path, timeout_s: int) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        list(args),
        cwd=str(cwd),
        text=True,
        capture_output=True,
        timeout=timeout_s,
        check=False,
    )


def strip_ansi(text: str) -> str:
    return RE_ANSI.sub("", text)


def extract_reason_codes(*blobs: str) -> List[str]:
    codes = set()
    for blob in blobs:
        codes.update(RE_REASON.findall(blob))
    return sorted(codes)


def choose_cli_bin(repo_root: Path, explicit: Optional[str], build_cli: bool) -> Path:
    if explicit:
        return Path(explicit).expanduser().resolve()

    metadata = run_cmd(
        ["cargo", "metadata", "--format-version", "1", "--no-deps"],
        cwd=repo_root,
        timeout_s=120,
    )
    if metadata.returncode != 0:
        raise RuntimeError(
            f"cargo metadata failed\nstdout:\n{metadata.stdout}\nstderr:\n{metadata.stderr}"
        )

    target_dir = Path(json.loads(metadata.stdout)["target_directory"])
    cli_bin = target_dir / "debug" / ("cli.exe" if os.name == "nt" else "cli")

    if build_cli:
        build = run_cmd(["cargo", "build", "-p", "cli"], cwd=repo_root, timeout_s=900)
        if build.returncode != 0:
            raise RuntimeError(
                f"cargo build -p cli failed\nstdout:\n{build.stdout}\nstderr:\n{build.stderr}"
            )

    if not cli_bin.exists():
        raise RuntimeError(
            f"CLI binary not found at {cli_bin}. Pass --cli-bin or enable build."
        )
    return cli_bin


def normalize_failure_text(text: str) -> str:
    text = strip_ansi(text)
    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    keep: List[str] = []
    for line in lines:
        if line.startswith("Warning:"):
            continue
        keep.append(line)
        if len(keep) >= 6:
            break
    if not keep:
        keep = lines[:3]
    joined = " | ".join(keep)
    joined = re.sub(r"/[^ ]+", "<path>", joined)
    joined = re.sub(r"[0-9]{2,}", "<n>", joined)
    return joined[:400]


def fingerprint_failure(stage: str, reason_codes: Sequence[str], detail: str) -> str:
    basis = f"{stage}::{','.join(reason_codes) or 'NO_CODE'}::{detail}"
    return hashlib.sha256(basis.encode("utf-8")).hexdigest()[:16]


def load_history(path: Optional[Path]) -> Dict[str, dict]:
    if path is None or not path.exists():
        return {}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {}
    if not isinstance(data, dict):
        return {}
    return data


def save_history(path: Optional[Path], payload: Dict[str, dict]) -> None:
    if path is None:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")


def promote_failure(
    promote_dir: Path,
    fingerprint: str,
    source: str,
    stage: str,
    reason_codes: Sequence[str],
) -> Path:
    promote_dir.mkdir(parents=True, exist_ok=True)
    out = promote_dir / f"{fingerprint}.lrl"
    if out.exists():
        return out

    header = [
        f";; auto-stress regression fingerprint: {fingerprint}",
        f";; stage: {stage}",
        f";; reason_codes: {','.join(reason_codes) if reason_codes else 'none'}",
        ";; generated_by: scripts/backend_auto_stress.py",
        "",
    ]
    out.write_text("\n".join(header) + source + "\n", encoding="utf-8")
    return out


def run_case(
    case_index: int,
    template_name: str,
    source: str,
    source_path: Path,
    output_bin: Path,
    cli_bin: Path,
    repo_root: Path,
    timeout_s: int,
    backend: str,
) -> CaseResult:
    source_path.write_text(source + "\n", encoding="utf-8")

    compile_proc = run_cmd(
        [
            str(cli_bin),
            "compile",
            str(source_path),
            "--backend",
            backend,
            "-o",
            str(output_bin),
        ],
        cwd=repo_root,
        timeout_s=timeout_s,
    )

    compile_stdout = strip_ansi(compile_proc.stdout)
    compile_stderr = strip_ansi(compile_proc.stderr)
    fallback_codes = extract_reason_codes(compile_stdout, compile_stderr)

    binary_exists = output_bin.exists()
    compile_failed = compile_proc.returncode != 0 or not binary_exists
    if compile_failed:
        detail = normalize_failure_text(compile_stdout + "\n" + compile_stderr)
        if not binary_exists:
            detail = (
                f"{detail} | expected output binary missing: {output_bin}"
                if detail
                else f"expected output binary missing: {output_bin}"
            )
        fp = fingerprint_failure("compile", fallback_codes, detail)
        return CaseResult(
            index=case_index,
            template=template_name,
            source_path=source_path,
            compile_ok=False,
            run_ok=False,
            backend=backend,
            fallback_codes=fallback_codes,
            compile_exit=compile_proc.returncode,
            run_exit=-1,
            compile_stdout=compile_stdout,
            compile_stderr=compile_stderr,
            run_stdout="",
            run_stderr="",
            failure_fingerprint=fp,
        )

    run_proc = run_cmd([str(output_bin)], cwd=repo_root, timeout_s=timeout_s)
    run_stdout = strip_ansi(run_proc.stdout)
    run_stderr = strip_ansi(run_proc.stderr)

    if run_proc.returncode != 0:
        detail = normalize_failure_text(run_stdout + "\n" + run_stderr)
        fp = fingerprint_failure("run", fallback_codes, detail)
        return CaseResult(
            index=case_index,
            template=template_name,
            source_path=source_path,
            compile_ok=True,
            run_ok=False,
            backend=backend,
            fallback_codes=fallback_codes,
            compile_exit=compile_proc.returncode,
            run_exit=run_proc.returncode,
            compile_stdout=compile_stdout,
            compile_stderr=compile_stderr,
            run_stdout=run_stdout,
            run_stderr=run_stderr,
            failure_fingerprint=fp,
        )

    return CaseResult(
        index=case_index,
        template=template_name,
        source_path=source_path,
        compile_ok=True,
        run_ok=True,
        backend=backend,
        fallback_codes=fallback_codes,
        compile_exit=compile_proc.returncode,
        run_exit=run_proc.returncode,
        compile_stdout=compile_stdout,
        compile_stderr=compile_stderr,
        run_stdout=run_stdout,
        run_stderr=run_stderr,
        failure_fingerprint=None,
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--count", type=int, default=50, help="number of generated programs")
    parser.add_argument(
        "--backend",
        choices=["auto", "typed", "dynamic"],
        default="auto",
        help="backend mode passed to `cli compile --backend`",
    )
    parser.add_argument("--seed", type=int, default=20260206, help="RNG seed")
    parser.add_argument(
        "--timeout-seconds",
        type=int,
        default=120,
        help="timeout for each compile/run subprocess",
    )
    parser.add_argument(
        "--report",
        type=Path,
        default=Path("ci/backend_auto_stress_report.json"),
        help="JSON report output path",
    )
    parser.add_argument(
        "--history-file",
        type=Path,
        default=None,
        help="optional JSON file storing cross-run failure counts",
    )
    parser.add_argument(
        "--promote-recurring",
        action="store_true",
        help="write recurring failures into regression .lrl files",
    )
    parser.add_argument(
        "--promote-threshold",
        type=int,
        default=2,
        help="count threshold for recurring-failure promotion",
    )
    parser.add_argument(
        "--promote-dir",
        type=Path,
        default=Path("tests/auto_stress_regressions"),
        help="where recurring failure repro cases are written",
    )
    parser.add_argument(
        "--keep-cases-dir",
        type=Path,
        default=None,
        help="copy generated source files to this directory",
    )
    parser.add_argument(
        "--cli-bin",
        type=str,
        default=None,
        help="path to prebuilt cli binary (defaults to cargo target debug binary)",
    )
    parser.add_argument(
        "--skip-build-cli",
        action="store_true",
        help="do not build cli before running stress",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    repo_root = Path(__file__).resolve().parents[1]

    cli_bin = choose_cli_bin(repo_root, args.cli_bin, build_cli=not args.skip_build_cli)
    rng = random.Random(args.seed)

    history = load_history(args.history_file)
    history.setdefault("fingerprints", {})

    report_cases: List[dict] = []
    failures: List[CaseResult] = []
    fallback_code_counts: Dict[str, int] = {}
    run_fingerprint_counts: Dict[str, int] = {}
    promoted: List[str] = []

    work_dir = Path(tempfile.mkdtemp(prefix="lrl_auto_stress_"))
    cases_dir = work_dir / "cases"
    bins_dir = work_dir / "bins"
    cases_dir.mkdir(parents=True, exist_ok=True)
    bins_dir.mkdir(parents=True, exist_ok=True)

    try:
        for idx in range(args.count):
            template_name, template_fn = rng.choice(TEMPLATES)
            source = template_fn(rng, idx)

            source_path = cases_dir / f"case_{idx:04d}_{template_name}.lrl"
            output_bin = bins_dir / f"case_{idx:04d}_bin"

            result = run_case(
                case_index=idx,
                template_name=template_name,
                source=source,
                source_path=source_path,
                output_bin=output_bin,
                cli_bin=cli_bin,
                repo_root=repo_root,
                timeout_s=args.timeout_seconds,
                backend=args.backend,
            )

            for code in result.fallback_codes:
                fallback_code_counts[code] = fallback_code_counts.get(code, 0) + 1

            case_json = {
                "index": idx,
                "template": template_name,
                "backend": result.backend,
                "compile_ok": result.compile_ok,
                "run_ok": result.run_ok,
                "compile_exit": result.compile_exit,
                "run_exit": result.run_exit,
                "fallback_codes": result.fallback_codes,
                "failure_fingerprint": result.failure_fingerprint,
                "source_path": str(result.source_path),
            }

            if not result.compile_ok or not result.run_ok:
                failures.append(result)
                assert result.failure_fingerprint is not None
                fp = result.failure_fingerprint
                run_fingerprint_counts[fp] = run_fingerprint_counts.get(fp, 0) + 1

                hist = history["fingerprints"].setdefault(
                    fp,
                    {
                        "count": 0,
                        "first_seen": now_iso(),
                        "example_template": template_name,
                        "reason_codes": result.fallback_codes,
                    },
                )
                hist["count"] = int(hist.get("count", 0)) + 1
                hist["last_seen"] = now_iso()

                if args.promote_recurring and run_fingerprint_counts[fp] >= args.promote_threshold:
                    promoted_path = promote_failure(
                        promote_dir=(repo_root / args.promote_dir),
                        fingerprint=fp,
                        source=source,
                        stage="compile" if not result.compile_ok else "run",
                        reason_codes=result.fallback_codes,
                    )
                    if str(promoted_path) not in promoted:
                        promoted.append(str(promoted_path))

                case_json["compile_stdout"] = result.compile_stdout
                case_json["compile_stderr"] = result.compile_stderr
                case_json["run_stdout"] = result.run_stdout
                case_json["run_stderr"] = result.run_stderr

            report_cases.append(case_json)

            if args.keep_cases_dir is not None:
                out_dir = repo_root / args.keep_cases_dir
                out_dir.mkdir(parents=True, exist_ok=True)
                shutil.copy2(source_path, out_dir / source_path.name)

        total = args.count
        compile_failures = sum(1 for c in report_cases if not c["compile_ok"])
        run_failures = sum(1 for c in report_cases if c["compile_ok"] and not c["run_ok"])
        success = total - compile_failures - run_failures

        report = {
            "timestamp": now_iso(),
            "seed": args.seed,
            "count": total,
            "backend": args.backend,
            "summary": {
                "success": success,
                "compile_failures": compile_failures,
                "run_failures": run_failures,
            },
            "fallback_reason_counts": dict(sorted(fallback_code_counts.items())),
            "promoted_regressions": promoted,
            "cases": report_cases,
        }

        report_path = repo_root / args.report
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(json.dumps(report, indent=2, sort_keys=True), encoding="utf-8")
        save_history((repo_root / args.history_file) if args.history_file else None, history)

        print(
            "backend-stress summary: "
            f"count={total}, success={success}, "
            f"compile_failures={compile_failures}, run_failures={run_failures}"
        )
        if fallback_code_counts:
            print("fallback reason codes:", json.dumps(dict(sorted(fallback_code_counts.items()))))
        print(f"report: {report_path}")

        return 0 if not failures else 1
    finally:
        shutil.rmtree(work_dir, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
