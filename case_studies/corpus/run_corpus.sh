#!/usr/bin/env bash
# Runs the ownership validation corpus described by manifest.tsv and writes results_corpus.md.
#
# Usage (from anywhere):
#   case_studies/corpus/run_corpus.sh
#
# Environment:
#   LRL           CLI binary to use. Default: build it with `cargo build -p cli` and use
#                 ${CARGO_TARGET_DIR:-<repo>/target}/debug/cli.
#   OUT_DIR       Directory for the raw outputs of every command (default: a fresh mktemp dir).
#   SKIP_COMPILE  If set to 1, positives are only checked with `run` (no native binaries).
#   SKIP_TYPED    If set to 1, the informational typed-backend column is not computed.
#
# For every manifest row the script runs `lrl run <file>` on the hand-written file and on its
# macro twin (cwd = repository root, which the CLI needs to find stdlib/), strips ANSI colours,
# and extracts the first diagnostic code of an `Error:` line. Positives are additionally compiled
# with `lrl compile <file> --backend dynamic -o <tmp>` and the binary is executed; the hand-written
# positives are also compiled with `--backend typed` (informational column).
# Exit status: 0 if every row matches its expectation, 1 otherwise.

set -u

CORPUS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$CORPUS_DIR/../.." && pwd)"
MANIFEST="$CORPUS_DIR/manifest.tsv"
RESULTS="$CORPUS_DIR/results_corpus.md"

if [ -z "${LRL:-}" ]; then
  (cd "$ROOT" && cargo build -p cli) || { echo "cargo build -p cli failed" >&2; exit 2; }
  LRL="${CARGO_TARGET_DIR:-$ROOT/target}/debug/cli"
fi
if [ ! -x "$LRL" ]; then
  echo "CLI binary not found or not executable: $LRL" >&2
  exit 2
fi
OUT_DIR="${OUT_DIR:-$(mktemp -d)}"
mkdir -p "$OUT_DIR"

strip_ansi() { sed $'s/\x1b\\[[0-9;]*m//g'; }

stage_of() {
  case "$1" in
    -) echo "accepted" ;;
    F0104) echo "macro_boundary" ;;
    F01*) echo "macro" ;;
    F00*) echo "parser" ;;
    F*) echo "elaborator" ;;
    K*) echo "kernel" ;;
    M*) echo "MIR" ;;
    TB*) echo "typed_backend" ;;
    C*) echo "driver" ;;
    *) echo "unknown" ;;
  esac
}

# run_file <file> <tag>: sets R_EXIT, R_CODE, R_STAGE, R_FIRST, R_LOG
run_file() {
  local file="$1" tag="$2"
  R_LOG="$OUT_DIR/$tag.run.log"
  (cd "$ROOT" && "$LRL" run "case_studies/corpus/$file") >"$R_LOG.raw" 2>&1
  R_EXIT=$?
  strip_ansi <"$R_LOG.raw" >"$R_LOG"
  rm -f "$R_LOG.raw"
  R_FIRST="$(grep -m1 -E '^Error: \[[A-Z]+[0-9]+\]' "$R_LOG" || true)"
  if [ -n "$R_FIRST" ]; then
    R_CODE="$(printf '%s\n' "$R_FIRST" | sed -E 's/^Error: \[([A-Z]+[0-9]+)\].*/\1/')"
  elif [ "$R_EXIT" -eq 0 ] && ! grep -q '^Error' "$R_LOG"; then
    R_CODE="-"
  else
    R_CODE="?"
    R_FIRST="$(grep -m1 '^Error' "$R_LOG" || echo "exit status $R_EXIT without an error line")"
  fi
  R_STAGE="$(stage_of "$R_CODE")"
}

# has_macro_label <log>: "yes" if a post-expansion diagnostic carries a macro call-site label
has_macro_label() {
  if grep -qE "macro '[^']+' expanded here|in code produced by macro '[^']+'|macro expansion: " "$1"; then
    echo "yes"
  else
    echo "no"
  fi
}

# compile_and_run <file> <backend> <tag>: sets C_STATUS (built|nobin) and C_OUT (binary output, one line)
compile_and_run() {
  local file="$1" backend="$2" tag="$3"
  local bin="$OUT_DIR/$tag.$backend.bin"
  local log="$OUT_DIR/$tag.$backend.compile.log"
  rm -f "$bin"
  (cd "$ROOT" && "$LRL" compile "case_studies/corpus/$file" --backend "$backend" -o "$bin") >"$log.raw" 2>&1
  strip_ansi <"$log.raw" >"$log"
  rm -f "$log.raw"
  if [ -x "$bin" ]; then
    C_STATUS="built"
    "$bin" >"$OUT_DIR/$tag.$backend.out" 2>&1
    C_OUT="$(tr '\n' ' ' <"$OUT_DIR/$tag.$backend.out" | sed 's/  *$//')"
  else
    C_STATUS="nobin"
    C_OUT="$(grep -m1 -E 'error|Error' "$log" || echo 'no binary')"
  fi
}

md_escape() { printf '%s' "$1" | sed 's/|/\\|/g' | cut -c1-220; }

neg_table=""
pos_table=""
detail_table=""
total=0
matched=0
twin_code_mismatch=""

while IFS=$'\t' read -r class kind file twin stage code frag tstage tcode tfrag desc; do
  case "$class" in "#"*|class|"") continue ;; esac
  total=$((total + 1))
  base="${file%.lrl}"
  tbase="${twin%.lrl}"

  run_file "$file" "$base"; h_exit=$R_EXIT; h_code=$R_CODE; h_stage=$R_STAGE; h_first=$R_FIRST; h_log=$R_LOG
  run_file "$twin" "$tbase"; t_exit=$R_EXIT; t_code=$R_CODE; t_stage=$R_STAGE; t_first=$R_FIRST; t_log=$R_LOG
  t_label="$(has_macro_label "$t_log")"

  h_frag_ok=yes; t_frag_ok=yes
  if [ "$kind" != "positive" ]; then
    if [ "$frag" != "-" ] && ! grep -qF -- "$frag" "$h_log"; then h_frag_ok=no; fi
    if [ "$tfrag" != "-" ] && ! grep -qF -- "$tfrag" "$t_log"; then t_frag_ok=no; fi
  fi

  ok=yes
  [ "$h_code" = "$code" ] || ok=no
  [ "$t_code" = "$tcode" ] || ok=no
  [ "$h_frag_ok" = yes ] && [ "$t_frag_ok" = yes ] || ok=no
  if [ "$code" = "-" ]; then [ "$h_exit" -eq 0 ] || ok=no; else [ "$h_exit" -ne 0 ] || ok=no; fi
  if [ "$tcode" = "-" ]; then [ "$t_exit" -eq 0 ] || ok=no; else [ "$t_exit" -ne 0 ] || ok=no; fi
  if [ "$kind" = "negative" ] && [ "$h_code" != "$t_code" ]; then
    twin_code_mismatch="$twin_code_mismatch $class"
  fi

  if [ "$kind" = "positive" ]; then
    hd="-"; td="-"; ty="(skipped)"
    if [ "${SKIP_COMPILE:-0}" != "1" ]; then
      compile_and_run "$file" dynamic "$base"; hd="$C_OUT"
      case "$hd" in *"$frag"*) ;; *) ok=no ;; esac
      compile_and_run "$twin" dynamic "$tbase"; td="$C_OUT"
      case "$td" in *"$tfrag"*) ;; *) ok=no ;; esac
      if [ "${SKIP_TYPED:-0}" != "1" ]; then
        compile_and_run "$file" typed "$base"; ty="$C_STATUS: $C_OUT"
      fi
    fi
    [ "$ok" = yes ] && matched=$((matched + 1))
    pos_table="$pos_table| $class | \`$file\` | exit $h_exit / exit $t_exit | $(md_escape "$hd") | $(md_escape "$td") | $(md_escape "$ty") | $ok |
"
    echo "[$class] $file run=$h_exit twin_run=$t_exit dyn='$hd' twin_dyn='$td' typed='$ty' match=$ok"
  else
    [ "$ok" = yes ] && matched=$((matched + 1))
    neg_table="$neg_table| $class | \`$file\` | $stage $code | $h_stage $h_code (exit $h_exit) | $t_stage $t_code (exit $t_exit) | $t_label | $ok |
"
    detail_table="$detail_table| \`$file\` | $(md_escape "${h_first:--}") |
| \`$twin\` | $(md_escape "${t_first:--}") |
"
    echo "[$class] $file -> $h_stage $h_code (exit $h_exit); twin -> $t_stage $t_code (exit $t_exit, label $t_label); match=$ok"
  fi
done <"$MANIFEST"

sha="$( (shasum -a 256 "$LRL" 2>/dev/null || sha256sum "$LRL") | awk '{print $1}')"
head_rev="$(cd "$ROOT" && git rev-parse --short HEAD 2>/dev/null || echo unknown)"
# Modified tracked files, not counting results files (which reruns of the scripts rewrite).
dirty="$(cd "$ROOT" && git status --porcelain --untracked-files=no -- . ':!**/results_*.md' ':!**/SUMMARY.md' ':!bench/results' ':!paper' 2>/dev/null | grep -v '^error' | wc -l | tr -d ' ')"

{
  echo "# Ownership validation corpus — results"
  echo
  echo "Generated by \`case_studies/corpus/run_corpus.sh\` (do not edit by hand)."
  echo
  echo "- Date (UTC): $(date -u '+%Y-%m-%d %H:%M:%S')"
  echo "- CLI binary: \`$LRL\` (sha256 \`$sha\`)"
  echo "- Repository: HEAD \`$head_rev\`, $dirty modified tracked file(s) other than results files at run time"
  echo "- Commands per file (cwd = repository root): \`lrl run case_studies/corpus/<file>\`; positives also"
  echo "  \`lrl compile case_studies/corpus/<file> --backend dynamic -o <tmp>\` followed by running the binary;"
  echo "  hand-written positives also \`--backend typed\` (informational)."
  echo "- Observed code = the first \`Error: [CODE]\` line of the output (ANSI colours stripped); \`-\` = no error and exit status 0."
  echo "- Stage from the code: F0104 macro_boundary, other F01xx macro, F02xx elaborator, K kernel, M MIR."
  echo "- Raw outputs: \`$OUT_DIR\`"
  echo
  echo "**$matched of $total manifest rows match their expectation.**"
  if [ -n "$twin_code_mismatch" ]; then
    echo
    echo "**Macro twins with a different first code than their hand-written version:$twin_code_mismatch**"
  else
    echo
    echo "Every macro twin of a violation class produced the same first diagnostic code as its hand-written version."
  fi
  echo
  echo "## Violation classes"
  echo
  echo "A row matches when both files exit non-zero (except an accepted hand-written \`macro_only\` file), the observed"
  echo "codes equal the manifest's, and the manifest's message fragment occurs in each output. \"Twin label\" records"
  echo "whether the twin's diagnostic carries a macro call-site label (\"macro 'm' expanded here\" / \"in code produced by macro 'm'\")."
  echo
  echo "| class | file (twin = \`*_macro.lrl\`) | expected stage / code | observed | twin observed | twin label | match |"
  echo "|---|---|---|---|---|---|---|"
  printf '%s' "$neg_table"
  echo
  echo "## Positive controls"
  echo
  echo "A row matches when both files are accepted by \`run\` (exit 0, no error) and both dynamic binaries print the"
  echo "manifest's expected line. The typed column is informational (not part of the match)."
  echo
  echo "| class | file (twin = \`*_macro.lrl\`) | run (file / twin) | dynamic binary (file) | dynamic binary (twin) | typed binary (file) | match |"
  echo "|---|---|---|---|---|---|---|"
  printf '%s' "$pos_table"
  echo
  echo "## First error line of every rejected or accepted violation-class file"
  echo
  echo "| file | first \`Error:\` line (verbatim, truncated) |"
  echo "|---|---|"
  printf '%s' "$detail_table"
} >"$RESULTS"

echo "wrote $RESULTS ($matched/$total rows match); raw outputs in $OUT_DIR"
[ "$matched" -eq "$total" ]
