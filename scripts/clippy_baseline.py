#!/usr/bin/env python3
"""Record and enforce a clippy warning baseline.

Usage:
  python3 scripts/clippy_baseline.py update
  python3 scripts/clippy_baseline.py check
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_BASELINE = REPO_ROOT / "ci" / "clippy-baseline.json"
CLIPPY_COMMAND = ["cargo", "clippy", "--all", "--all-targets", "--message-format=json"]


@dataclass(frozen=True)
class WarningKey:
    code: str
    path: str
    message: str


def _normalize_workspace_path(file_name: str) -> str | None:
    path = Path(file_name)
    if not path.is_absolute():
        path = (REPO_ROOT / path).resolve()
    else:
        path = path.resolve()
    try:
        return path.relative_to(REPO_ROOT).as_posix()
    except ValueError:
        return None


def _extract_warning_key(message: dict) -> WarningKey | None:
    if message.get("level") != "warning":
        return None

    raw_code = message.get("code")
    if isinstance(raw_code, dict):
        code = raw_code.get("code") or "unknown-warning"
    else:
        code = "unknown-warning"
    spans = message.get("spans", [])
    primary = next((span for span in spans if span.get("is_primary")), None)
    chosen_span = primary or (spans[0] if spans else None)
    if not chosen_span:
        return None

    normalized_path = _normalize_workspace_path(chosen_span.get("file_name", ""))
    if not normalized_path:
        return None

    text = (message.get("message") or "").strip()
    return WarningKey(code=code, path=normalized_path, message=text)


def collect_warnings() -> Counter[WarningKey]:
    proc = subprocess.run(
        CLIPPY_COMMAND,
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )

    warnings: list[WarningKey] = []
    errors: list[tuple[str, str]] = []
    for line in proc.stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            payload = json.loads(line)
        except json.JSONDecodeError:
            continue
        if payload.get("reason") != "compiler-message":
            continue
        message = payload.get("message", {})
        if message.get("level") == "error":
            spans = message.get("spans", [])
            primary = next((span for span in spans if span.get("is_primary")), None)
            chosen_span = primary or (spans[0] if spans else None)
            raw_path = chosen_span.get("file_name", "") if chosen_span else ""
            path = _normalize_workspace_path(raw_path) or raw_path or "<unknown>"
            errors.append((path, (message.get("message") or "").strip()))
        key = _extract_warning_key(message)
        if key is not None:
            warnings.append(key)

    if proc.returncode != 0:
        if proc.stderr.strip():
            print(proc.stderr.strip(), file=sys.stderr)
        if errors:
            print("Clippy reported hard errors:", file=sys.stderr)
            for path, msg in errors[:20]:
                print(f"  - {path}: {msg}", file=sys.stderr)
            if len(errors) > 20:
                print(f"  ... and {len(errors) - 20} more", file=sys.stderr)
        raise RuntimeError(f"clippy exited with status {proc.returncode}")

    return Counter(warnings)


def counter_to_json(counter: Counter[WarningKey]) -> dict:
    rows = [
        {
            "code": key.code,
            "path": key.path,
            "message": key.message,
            "count": count,
        }
        for key, count in sorted(
            counter.items(),
            key=lambda item: (item[0].code, item[0].path, item[0].message),
        )
    ]
    return {
        "version": 1,
        "generated_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "cargo_command": " ".join(CLIPPY_COMMAND),
        "warning_count_total": sum(counter.values()),
        "warning_count_unique": len(counter),
        "warnings": rows,
    }


def json_to_counter(payload: dict) -> Counter[WarningKey]:
    counter: Counter[WarningKey] = Counter()
    for row in payload.get("warnings", []):
        key = WarningKey(
            code=row["code"],
            path=row["path"],
            message=row["message"],
        )
        counter[key] += int(row.get("count", 1))
    return counter


def _print_list(header: str, entries: Iterable[tuple[WarningKey, int]]) -> None:
    print(header)
    for key, count in entries:
        print(f"  - [{key.code}] {key.path} (count={count}): {key.message}")


def update_baseline(baseline_path: Path) -> int:
    counter = collect_warnings()
    payload = counter_to_json(counter)
    baseline_path.parent.mkdir(parents=True, exist_ok=True)
    baseline_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(
        f"Wrote baseline to {baseline_path} "
        f"(total={payload['warning_count_total']}, unique={payload['warning_count_unique']})."
    )
    return 0


def check_baseline(baseline_path: Path) -> int:
    if not baseline_path.exists():
        print(
            f"Baseline file not found: {baseline_path}\n"
            f"Run: python3 scripts/clippy_baseline.py update",
            file=sys.stderr,
        )
        return 2

    baseline_payload = json.loads(baseline_path.read_text())
    baseline_counter = json_to_counter(baseline_payload)
    current_counter = collect_warnings()

    added = []
    increased = []
    for key, current_count in current_counter.items():
        baseline_count = baseline_counter.get(key, 0)
        if baseline_count == 0:
            added.append((key, current_count))
        elif current_count > baseline_count:
            increased.append((key, current_count - baseline_count))

    print(
        "Clippy baseline summary: "
        f"baseline(total={sum(baseline_counter.values())}, unique={len(baseline_counter)}), "
        f"current(total={sum(current_counter.values())}, unique={len(current_counter)})."
    )

    if not added and not increased:
        print("Clippy warnings did not regress.")
        return 0

    if added:
        _print_list("New warnings:", sorted(added, key=lambda item: (item[0].code, item[0].path, item[0].message)))
    if increased:
        _print_list(
            "Existing warnings with increased count:",
            sorted(increased, key=lambda item: (item[0].code, item[0].path, item[0].message)),
        )
    print(
        "\nIf this increase is intentional, refresh the baseline:\n"
        "  python3 scripts/clippy_baseline.py update",
        file=sys.stderr,
    )
    return 1


def main() -> int:
    parser = argparse.ArgumentParser(description="Maintain clippy warning baseline.")
    parser.add_argument(
        "command",
        choices=["update", "check"],
        help="Update the baseline file or check against it.",
    )
    parser.add_argument(
        "--baseline",
        default=str(DEFAULT_BASELINE),
        help=f"Baseline file path (default: {DEFAULT_BASELINE}).",
    )
    args = parser.parse_args()

    baseline_path = Path(args.baseline)
    if not baseline_path.is_absolute():
        baseline_path = (REPO_ROOT / baseline_path).resolve()

    if args.command == "update":
        return update_baseline(baseline_path)
    return check_baseline(baseline_path)


if __name__ == "__main__":
    raise SystemExit(main())
