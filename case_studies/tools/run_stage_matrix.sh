#!/usr/bin/env bash
# Stage matrix over the validation corpus and the program corpus.
#
#   case_studies/tools/run_stage_matrix.sh
#
# 1. builds case_studies/tools/stage_matrix (a stand-alone cargo project, not a workspace member);
# 2. runs it on every .lrl file of the sets below (from the repository root, like the CLI), one
#    process per file, writing JSON lines to $OUT/<backend>/<set>.jsonl;
# 3. writes case_studies/tools/results_stage_matrix.md (summarize.py), whose header records the
#    repository commit and the SHA-256 of the stage_matrix tool binary and of the CLI binary used
#    for the cross-check (if any).
#
# Environment overrides:
#   STAGE_MATRIX_TARGET_DIR  cargo target dir for the tool  (default: case_studies/tools/stage_matrix/target)
#   STAGE_MATRIX_BACKENDS    prelude stacks to use          (default: "dynamic typed"; dynamic = `lrl run`,
#                                                             typed = `lrl compile --backend typed|auto`)
#   STAGE_MATRIX_JOBS        parallel files                 (default: 4)
#   STAGE_MATRIX_TIMEOUT     seconds per file               (default: 600)
#   STAGE_MATRIX_OUT         JSON-lines output directory    (default: case_studies/tools/stage_matrix_results)
#   STAGE_MATRIX_CLI         optional path to a CLI binary built from the same tree (e.g. target/debug/cli):
#                            if set, every file of the dynamic run is also run with `<cli> run <file>` and the
#                            error codes are compared with the replay (check_against_cli.py)
set -euo pipefail

TOOLS="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$TOOLS/../.." && pwd)"
TOOL_DIR="$TOOLS/stage_matrix"
TARGET="${STAGE_MATRIX_TARGET_DIR:-$TOOL_DIR/target}"
BACKENDS="${STAGE_MATRIX_BACKENDS:-dynamic typed}"
JOBS="${STAGE_MATRIX_JOBS:-4}"
TIMEOUT_S="${STAGE_MATRIX_TIMEOUT:-600}"
OUT="${STAGE_MATRIX_OUT:-$TOOLS/stage_matrix_results}"

echo "[stage-matrix] building the tool (CARGO_TARGET_DIR=$TARGET)"
(cd "$TOOL_DIR" && CARGO_TARGET_DIR="$TARGET" cargo build --quiet)
BIN="$TARGET/debug/stage_matrix"

# SHA-256 (hex) of a file: shasum (macOS) or sha256sum (Linux).
sha256_of() {
  if command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | awk '{print $1}'
  else
    sha256sum "$1" | awk '{print $1}'
  fi
}
TOOL_SHA="$(sha256_of "$BIN")"
echo "[stage-matrix] tool binary $BIN sha256 $TOOL_SHA"

# Sets: name=directory (relative to the repository root). Missing directories are skipped.
# `packages/` fixtures are excluded (they need the package manager, as in cli/tests/lrl_corpus_expectations.rs).
SETS=(
  "corpus=case_studies/corpus"
  "case_studies=case_studies/lrl"
  "tests=tests"
  "code_examples=code_examples"
  "mir_gaps=case_studies/tools/stage_matrix/gaps"
)

rm -rf "$OUT/dynamic" "$OUT/typed" "$OUT/cli_check.json"
mkdir -p "$OUT"
for backend in $BACKENDS; do
  python3 "$TOOL_DIR/run_matrix.py" --bin "$BIN" --root "$ROOT" --out "$OUT" \
    --backend "$backend" --jobs "$JOBS" --timeout "$TIMEOUT_S" "${SETS[@]}"
done

CLI_ARGS=()
if [[ -n "${STAGE_MATRIX_CLI:-}" && " $BACKENDS " == *" dynamic "* ]]; then
  CLI_SHA="$(sha256_of "$STAGE_MATRIX_CLI")"
  echo "[stage-matrix] CLI binary $STAGE_MATRIX_CLI sha256 $CLI_SHA"
  (cd "$ROOT" && python3 "$TOOL_DIR/check_against_cli.py" --cli "$STAGE_MATRIX_CLI" --results "$OUT" \
    --out "$OUT/cli_check.json" --jobs "$JOBS" --timeout "$TIMEOUT_S")
  CLI_ARGS=(--cli-sha256 "$CLI_SHA")
fi

python3 "$TOOL_DIR/summarize.py" --results "$OUT" --root "$ROOT" \
  --out "$TOOLS/results_stage_matrix.md" --command "case_studies/tools/run_stage_matrix.sh" \
  --tool-sha256 "$TOOL_SHA" ${CLI_ARGS[@]+"${CLI_ARGS[@]}"}
echo "[stage-matrix] wrote $TOOLS/results_stage_matrix.md"
