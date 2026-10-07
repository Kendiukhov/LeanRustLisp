#!/usr/bin/env bash
# Rerun every Lean 4 and Idris 2 comparison program and write results_lean_idris.md
# (same table format as results_rust_racket.md).
#
# Usage:  case_studies/comparison/run_lean_idris.sh
# Env:    CMP_BUILD_DIR  directory for build outputs and logs (default: a fresh mktemp directory).
#                        Nothing is written inside the repository except results_lean_idris.md.
# Needs:  lean + lake (elan toolchain leanprover/lean4:v4.34.1); idris2 0.8.0 with its Chez Scheme
#         back end and the `linear` and `contrib` packages.
# Compatible with the macOS system bash (3.2).
#
# Each case is compiled and, if compilation succeeds and the file has a `main`, run. Observed outcome:
#   ACCEPT         compiled (and, if it has `main`, ran with exit status 0)
#   COMPILE_ERROR  rejected before running (Lean elaboration / type error; Idris 2 type, linearity
#                  or coverage error; for Lean also a failed native build)
#   RUNTIME_ERROR  compiled, then failed when run (non-zero exit status, or killed after 60 s)
#
# Lean:    `lean FILE` (cwd lean/) type-checks the file and prints the compiler-IR traces the file
#          asks for; if it is accepted and has `main`, `lake build` builds a native executable from it
#          (lake package in $CMP_BUILD_DIR/lean/pkg whose source directory is a symlink to lean/).
# Idris 2: files with `main` are compiled with
#          `idris2 -p linear -p contrib --dumpcases CASES -o NAME FILE` (Chez Scheme back end) and the
#          executable is run; files without `main` are checked with `idris2 -p linear -p contrib --check`.

set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
BUILD="${CMP_BUILD_DIR:-$(mktemp -d "${TMPDIR:-/tmp}/lrl_cmp_li.XXXXXX")}"
OUT="$HERE/results_lean_idris.md"
LEAN_SRC="$HERE/lean"
IDRIS_SRC="$HERE/idris2"
LEAN_TOOLCHAIN="leanprover/lean4:v4.34.1"
LOGS="$BUILD/logs"
PKG="$BUILD/lean/pkg"
IBUILD="$BUILD/idris2"
RUN_LIMIT=60
rm -rf "$LOGS" "$PKG" "$IBUILD"
mkdir -p "$LOGS" "$PKG" "$IBUILD"

# ---------------------------------------------------------------------------------------------
# Cases: lang | Q | property | file | kind | expected | mode | arg
#   kind:  positive (should be accepted), negative (the property is violated: should be rejected;
#          expected = ACCEPT / RUNTIME_ERROR where the tool cannot reject it), limit (probes whether
#          the tool can express or enforce the property at all; "expected" is our prediction)
#   mode:  build  compile (and run, if the file has main)
#          ir     same compilation; the excerpt shows compiler intermediate output for the
#                 definitions named in arg (comma-separated): Lean final IR
#                 (trace.compiler.ir.result), Idris 2 case trees (--dumpcases).
#                 "names~re1/re2/..." selects parts of the output with extended regular
#                 expressions: for Lean, the first line of each IR block and the lines matching
#                 one of them; for Idris 2 (one line per case tree), the matching substrings.
#                 The full blocks are printed below the table in any case.
#          scheme Idris 2 only: whether the generated Chez Scheme definition named in arg
#                 contains `vector-set!` (a destructive vector update)
# ---------------------------------------------------------------------------------------------
CASES=$(cat <<'EOF'
lean|Q1|indexed vector, total head|Q1_head.lean|positive|ACCEPT|build|-
lean|Q1|indexed vector, total head|Q1_head.lean|positive|ACCEPT|ir|Vec.head,vectorHead._redArg
lean|Q1|indexed vector, total head|Q1_head_empty_neg.lean|negative|COMPILE_ERROR|build|-
lean|Q1|indexed vector, total head|Q1_vector_head_empty_neg.lean|negative|COMPILE_ERROR|build|-
lean|Q2|append, length = sum|Q2_append.lean|positive|ACCEPT|build|-
lean|Q2|append, length = sum|Q2_append_drop_neg.lean|negative|COMPILE_ERROR|build|-
lean|Q3|proof: reverse is an involution|Q3_reverse_involution.lean|positive|ACCEPT|build|-
lean|Q3|proof: reverse is an involution|Q3_reverse_wrong_neg.lean|negative|COMPILE_ERROR|build|-
lean|Q4|proofs/ghost values absent at run time|Q4_erasure.lean|positive|ACCEPT|build|-
lean|Q4|proofs/ghost values absent at run time|Q4_erasure.lean|positive|ACCEPT|ir|safeDiv,safeDiv._redArg,useSafeDiv
lean|Q4|proofs/ghost values absent at run time|Q4_erasure.lean|positive|ACCEPT|ir|vectorSize._redArg,mkPos
lean|Q4|proofs/ghost values absent at run time|Q4_erasure.lean|limit|ACCEPT|ir|Vec.push._redArg,Vec.len._redArg
lean|Q4|proofs/ghost values absent at run time|Q4_zero_divisor_neg.lean|negative|COMPILE_ERROR|build|-
lean|Q4|proofs/ghost values absent at run time|Q4_forge_neg.lean|negative|ACCEPT|build|-
lean|Q4|proofs/ghost values absent at run time|Q4_index_at_runtime_neg.lean|negative|ACCEPT|build|-
lean|Q5|single-use channel|Q5_channel.lean|positive|ACCEPT|build|-
lean|Q5|single-use channel|Q5_channel_reuse_neg.lean|negative|RUNTIME_ERROR|build|-
lean|Q6|wrong protocol state rejected|Q5_channel.lean|positive|ACCEPT|build|-
lean|Q6|wrong protocol state rejected|Q6_wrong_state_neg.lean|negative|COMPILE_ERROR|build|-
lean|Q7|protocol length = data length|Q7_send_vector.lean|positive|ACCEPT|build|-
lean|Q7|protocol length = data length|Q7_too_many_neg.lean|negative|COMPILE_ERROR|build|-
lean|Q7|protocol length = data length|Q7_too_few_neg.lean|negative|COMPILE_ERROR|build|-
lean|Q7|protocol length = data length|Q7_abandon_neg.lean|negative|ACCEPT|build|-
lean|Q8|hygienic macro generating typed ops|Q8_macro.lean|positive|ACCEPT|build|-
lean|Q8|hygienic macro generating typed ops|Q8_macro_ops_neg.lean|negative|COMPILE_ERROR|build|-
lean|Q8|hygienic macro generating typed ops|Q8_macro_global_names.lean|limit|ACCEPT|build|-
lean|Q9|two live mutable references to one location|Q9_two_refs.lean|positive|ACCEPT|build|-
lean|Q9|two live mutable references to one location|Q9_alias_neg.lean|negative|ACCEPT|build|-
lean|Q10|value consumed in both branches|Q10_branch_consume.lean|positive|ACCEPT|build|-
lean|Q10|value consumed in both branches|Q10_use_after_neg.lean|negative|RUNTIME_ERROR|build|-
lean|Q11|in-place update|Q11_inplace.lean|positive|ACCEPT|build|-
lean|Q11|in-place update|Q11_inplace.lean|positive|ACCEPT|ir|revAcc._redArg~isShared/set x_/ctor_1
lean|Q12|once-only closure called twice|Q12_once_fn_neg.lean|negative|ACCEPT|build|-
idris2|Q1|indexed vector, total head|Q1_head.idr|positive|ACCEPT|build|-
idris2|Q1|indexed vector, total head|Q1_head.idr|positive|ACCEPT|ir|Main.vhead,Data.Vect.head
idris2|Q1|indexed vector, total head|Q1_head_empty_neg.idr|negative|COMPILE_ERROR|build|-
idris2|Q2|append, length = sum|Q2_append.idr|positive|ACCEPT|build|-
idris2|Q2|append, length = sum|Q2_append_drop_neg.idr|negative|COMPILE_ERROR|build|-
idris2|Q3|proof: reverse is an involution|Q3_reverse_involution.idr|positive|ACCEPT|build|-
idris2|Q3|proof: reverse is an involution|Q3_reverse_wrong_neg.idr|negative|COMPILE_ERROR|build|-
idris2|Q4|proofs/ghost values absent at run time|Q4_erasure.idr|positive|ACCEPT|build|-
idris2|Q4|proofs/ghost values absent at run time|Q4_erasure.idr|positive|ACCEPT|ir|Main.safeDiv,Main.push,Main.vlength
idris2|Q4|proofs/ghost values absent at run time|Q4_erasure.idr|positive|ACCEPT|ir|Main.main~Main\.safeDiv \[[0-9, ]*\]/Main\.vlength \[[0-9]+
idris2|Q4|proofs/ghost values absent at run time|Q4_erased_index_neg.idr|negative|COMPILE_ERROR|build|-
idris2|Q4|proofs/ghost values absent at run time|Q4_zero_divisor_neg.idr|negative|COMPILE_ERROR|build|-
idris2|Q4|proofs/ghost values absent at run time|Q4_forge_neg.idr|negative|RUNTIME_ERROR|build|-
idris2|Q5|single-use channel|Q5_channel.idr|positive|ACCEPT|build|-
idris2|Q5|single-use channel|Q5_channel_reuse_neg.idr|negative|COMPILE_ERROR|build|-
idris2|Q6|wrong protocol state rejected|Q5_channel.idr|positive|ACCEPT|build|-
idris2|Q6|wrong protocol state rejected|Q6_wrong_state_neg.idr|negative|COMPILE_ERROR|build|-
idris2|Q7|protocol length = data length|Q7_send_vector.idr|positive|ACCEPT|build|-
idris2|Q7|protocol length = data length|Q7_too_many_neg.idr|negative|COMPILE_ERROR|build|-
idris2|Q7|protocol length = data length|Q7_too_few_neg.idr|negative|COMPILE_ERROR|build|-
idris2|Q7|protocol length = data length|Q7_abandon_neg.idr|negative|COMPILE_ERROR|build|-
idris2|Q8|hygienic macro generating typed ops|Q8_macro.idr|positive|ACCEPT|build|-
idris2|Q8|hygienic macro generating typed ops|Q8_macro_ops_neg.idr|negative|COMPILE_ERROR|build|-
idris2|Q8|hygienic macro generating typed ops|Q8_macro_global_names.idr|limit|ACCEPT|build|-
idris2|Q8|hygienic macro generating typed ops|Q8_macro_global_ambiguous.idr|limit|COMPILE_ERROR|build|-
idris2|Q9|two live mutable references to one location|Q9_two_arrays.idr|positive|ACCEPT|build|-
idris2|Q9|two live mutable references to one location|Q9_alias_neg.idr|negative|COMPILE_ERROR|build|-
idris2|Q10|value consumed in both branches|Q10_branch_consume.idr|positive|ACCEPT|build|-
idris2|Q10|value consumed in both branches|Q10_use_after_neg.idr|negative|COMPILE_ERROR|build|-
idris2|Q10|value consumed in both branches|Q10_branch_drop_neg.idr|limit|COMPILE_ERROR|build|-
idris2|Q11|in-place update|Q11_inplace.idr|positive|ACCEPT|build|-
idris2|Q11|in-place update|Q11_inplace.idr|positive|ACCEPT|ir|Data.Linear.Array.write
idris2|Q11|in-place update|Q11_inplace.idr|positive|ACCEPT|scheme|DataC-45IOArray-writeArray
idris2|Q11|in-place update|Q11_inplace.idr|limit|ACCEPT|ir|Data.Linear.LVect.reverse
idris2|Q11|in-place update|Q11_array_reuse_neg.idr|negative|COMPILE_ERROR|build|-
idris2|Q12|once-only closure called twice|Q12_once_fn.idr|positive|ACCEPT|build|-
idris2|Q12|once-only closure called twice|Q12_once_fn_neg.idr|negative|COMPILE_ERROR|build|-
idris2|Q12|once-only closure called twice|Q12_capture_unrestricted_neg.idr|negative|COMPILE_ERROR|build|-
EOF
)

# ---------------------------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------------------------
md_escape() {
  # one line, no pipes or backticks, build paths shortened, at most 300 characters
  sed "s/$(printf '\033')\[[0-9;]*m//g" | tr '\n' ' ' | sed -e 's/|/\\|/g' -e 's/`/'"'"'/g' \
    -e "s#$BUILD#<build>#g" -e 's/[[:space:]][[:space:]]*/ /g' -e 's/^ //' -e 's/ $//' | cut -c1-300
}

base_of() { local f="$1"; f="${f%.lean}"; f="${f%.idr}"; echo "$f"; }

# Run "$@" with stdout+stderr to $1, killing it after $RUN_LIMIT seconds; returns its status.
run_limited() {
  local log="$1"; shift
  "$@" >"$log" 2>&1 &
  local pid=$!
  ( sleep "$RUN_LIMIT"; kill -9 "$pid" 2>/dev/null ) >/dev/null 2>&1 &
  local watchdog=$!
  wait "$pid"; local st=$?
  kill "$watchdog" 2>/dev/null; wait "$watchdog" 2>/dev/null
  return "$st"
}

first_lines() {
  # all non-empty lines of a run log (the excerpt is cut to 300 characters later)
  grep -v '^[[:space:]]*$' "$1"
}

lean_first_error() {
  # first Lean message containing ": error" with its continuation lines (until the next message)
  awk '
    /^[^ ]+\.lean:[0-9]+:[0-9]+: / { if (on) exit; if ($0 ~ /: error/) on=1 }
    on { print }' "$1"
}

idris_first_error() {
  # first "Error:" paragraph of an Idris 2 log, followed by its source location line
  awk '
    !on && /^Error:/ { on=1 }
    on == 1 { if ($0 ~ /^[[:space:]]*$/) { on=2; next } print; next }
    on == 2 { if ($0 !~ /^[[:space:]]*$/) { print; exit } }' "$1"
}

lean_ir_block() {
  # the final-IR block "def NAME (...)" from a Lean log (until the next def or trace header)
  awk -v name="$2" '
    $1 == "def" && $2 == name { on=1; print; next }
    on && ($1 == "def" || /^\[Compiler/ || /^[^ ]/) { on=0 }
    on { print }' "$1"
}

idris_case_tree() {
  # the case-tree line "NAME = ..." from an Idris 2 --dumpcases file
  grep -F "$2 = " "$1" | awk -v name="$2" 'index($0, name " = ") == 1' | head -n 1
}

# "a,b~re" -> "a b" (definition names of an ir case)
ir_names() { echo "${1%%~*}" | tr ',' ' '; }

has_main_lean()  { grep -q '^def main' "$1"; }
has_main_idris() { grep -q '^main :' "$1"; }

# ---------------------------------------------------------------------------------------------
# compile each distinct file once; record status files in $LOGS
#   <lang>_<base>.check.{txt,status}  Lean `lean FILE` / Idris 2 compile or --check
#   <lang>_<base>.build.{txt,status}  Lean native build (lake)
#   <lang>_<base>.run.{txt,status}    run of the executable
# ---------------------------------------------------------------------------------------------
LEAN_FILES="$(printf '%s\n' "$CASES" | awk -F'|' '$1=="lean"{print $4}' | awk '!seen[$0]++')"
IDRIS_FILES="$(printf '%s\n' "$CASES" | awk -F'|' '$1=="idris2"{print $4}' | awk '!seen[$0]++')"

echo "== Lean: lean FILE"
LEAN_EXES=""
for f in $LEAN_FILES; do
  b="$(base_of "$f")"; L="$LOGS/lean_$b"
  (cd "$LEAN_SRC" && lean "$f") >"$L.check.txt" 2>&1
  st=$?; echo "$st" >"$L.check.status"
  echo "   $f: exit $st"
  if [ "$st" -eq 0 ] && has_main_lean "$LEAN_SRC/$f"; then LEAN_EXES="$LEAN_EXES $b"; fi
done

echo "== Lean: lake build + run"
ln -sfn "$LEAN_SRC" "$PKG/src"
echo "$LEAN_TOOLCHAIN" >"$PKG/lean-toolchain"
{
  echo 'import Lake'
  echo 'open Lake DSL'
  echo 'package cmp where'
  echo '  srcDir := "src"'
  for b in $LEAN_EXES; do echo "lean_exe run_$b where root := \`$b"; done
} >"$PKG/lakefile.lean"
for b in $LEAN_EXES; do
  L="$LOGS/lean_$b"
  (cd "$PKG" && lake build "run_$b") >"$L.build.txt" 2>&1
  bst=$?; echo "$bst" >"$L.build.status"
  if [ "$bst" -eq 0 ]; then
    run_limited "$L.run.txt" "$PKG/.lake/build/bin/run_$b"
    echo "$?" >"$L.run.status"
  fi
  echo "   $b: lake build exit $bst, run exit $(cat "$L.run.status" 2>/dev/null || echo -)"
done

echo "== Idris 2: compile (or --check) + run"
for f in $IDRIS_FILES; do
  b="$(base_of "$f")"; L="$LOGS/idris2_$b"; d="$IBUILD/$b"
  mkdir -p "$d"
  if has_main_idris "$IDRIS_SRC/$f"; then
    (cd "$IDRIS_SRC" && idris2 --no-color -p linear -p contrib --build-dir "$d/build" \
       --output-dir "$d/exec" --dumpcases "$d/cases.txt" -o "$b" "$f") >"$L.check.txt" 2>&1
    st=$?
  else
    (cd "$IDRIS_SRC" && idris2 --no-color -p linear -p contrib --build-dir "$d/build" \
       --check "$f") >"$L.check.txt" 2>&1
    st=$?
  fi
  echo "$st" >"$L.check.status"
  # idris2 may leave an executable behind even when it reports errors: run only after exit 0
  if [ "$st" -eq 0 ] && [ -x "$d/exec/$b" ]; then
    run_limited "$L.run.txt" "$d/exec/$b"
    echo "$?" >"$L.run.status"
  fi
  echo "   $f: idris2 exit $st, run exit $(cat "$L.run.status" 2>/dev/null || echo -)"
done

# ---------------------------------------------------------------------------------------------
# classify every case
# ---------------------------------------------------------------------------------------------
classify() {
  # sets OBS and MSG for one case
  local lang="$1" file="$2" mode="$3" arg="$4"
  local b; b="$(base_of "$file")"
  local L="$LOGS/${lang}_$b"
  local cst; cst="$(cat "$L.check.status")"
  OBS=""; MSG=""
  if [ "$cst" -ne 0 ]; then
    OBS=COMPILE_ERROR
    if [ "$lang" = lean ]; then MSG="$(lean_first_error "$L.check.txt")"
    else MSG="$(idris_first_error "$L.check.txt")"; fi
    return
  fi
  if [ -f "$L.build.status" ] && [ "$(cat "$L.build.status")" -ne 0 ]; then
    OBS=COMPILE_ERROR; MSG="accepted by lean; native build failed: $(grep -m1 -i 'error' "$L.build.txt")"
    return
  fi
  if [ -f "$L.run.status" ]; then
    if [ "$(cat "$L.run.status")" -eq 0 ]; then OBS=ACCEPT; else OBS=RUNTIME_ERROR; fi
  else
    OBS=ACCEPT
  fi
  case "$mode" in
    build)
      if [ -f "$L.run.status" ]; then
        MSG="$(first_lines "$L.run.txt")"
        [ "$OBS" = RUNTIME_ERROR ] && MSG="$MSG (exit $(cat "$L.run.status"))"
      else
        MSG="accepted (no main): $(grep -v '^[[:space:]]*$' "$L.check.txt" | grep -v '^1/1: Building' | head -n 3)"
      fi ;;
    ir)
      local names n blk filt=""
      names="$(ir_names "$arg")"
      case "$arg" in *~*) filt="$(echo "${arg#*~}" | tr '/' '|')" ;; esac
      MSG=""
      for n in $names; do
        if [ "$lang" = lean ]; then blk="$(lean_ir_block "$L.check.txt" "$n")"
        else blk="$(idris_case_tree "$IBUILD/$b/cases.txt" "$n")"; fi
        if [ -n "$filt" ] && [ "$lang" = lean ]; then
          blk="$(printf '%s\n' "$blk" | awk -v re="$filt" 'NR == 1 || $0 ~ re')"
        elif [ -n "$filt" ]; then
          blk="$n contains: $(printf '%s\n' "$blk" | grep -oE "$filt" | sed 's/$/ .../' | tr '\n' ';' | sed 's/;$//; s/;/; /g')"
        fi
        MSG="$MSG $blk"
      done ;;
    scheme)
      local ss="$IBUILD/$b/exec/${b}_app/$b.ss"
      if grep "^(define $arg " "$ss" | grep -q 'vector-set!'; then
        MSG="generated Chez Scheme: (define $arg ...) contains vector-set!"
      else
        MSG="generated Chez Scheme: vector-set! NOT found in (define $arg ...)"
      fi ;;
  esac
}

ROWS=""
n=0; n_match=0
while IFS='|' read -r lang q prop file kind expected mode arg; do
  [ -z "$lang" ] && continue
  n=$((n + 1))
  classify "$lang" "$file" "$mode" "$arg"
  if [ "$OBS" = "$expected" ]; then m=yes; n_match=$((n_match + 1)); else m=NO; fi
  prog="$lang/$file"
  shown="$(ir_names "$arg" | sed 's/ /, /g')"
  case "$arg" in *~*) shown="$shown; selected lines" ;; esac
  if [ "$mode" = ir ] && [ "$lang" = lean ]; then prog="$prog [IR: $shown]"; fi
  if [ "$mode" = ir ] && [ "$lang" = idris2 ]; then prog="$prog [--dumpcases: $shown]"; fi
  if [ "$mode" = scheme ]; then prog="$prog [Chez Scheme: $arg]"; fi
  msg_md="$(printf '%s' "$MSG" | md_escape)"
  ROWS="$ROWS| $q | $prop | $lang | \`$prog\` | $kind | $expected | $OBS | $m | $msg_md |
"
  printf '%-4s %-6s %-48s %-7s %-14s %-14s %s\n' "$q" "$lang" "$file" "$mode" "$expected" "$OBS" "$m"
done <<<"$CASES"

# ---------------------------------------------------------------------------------------------
# tool versions
# ---------------------------------------------------------------------------------------------
LEAN_V="$(lean --version 2>&1 | head -n 1)"
LAKE_V="$(lake --version 2>&1 | head -n 1)"
ELAN_V="$(elan --version 2>&1 | head -n 1)"
IDRIS_V="$(idris2 --version 2>&1 | head -n 1)"
CHEZ_V="$(chez --version 2>&1 | head -n 1)"
IDRIS_LIBDIR="$(idris2 --libdir 2>/dev/null)"
IDRIS_PKGS="$(ls "$IDRIS_LIBDIR" 2>/dev/null | grep -E '^(base|contrib|linear|prelude)-' | tr '\n' ' ' | sed 's/ $//')"
OS_V="$(uname -srm 2>&1)"
if command -v sw_vers >/dev/null 2>&1; then OS_V="$OS_V; macOS $(sw_vers -productVersion)"; fi

# ---------------------------------------------------------------------------------------------
# report
# ---------------------------------------------------------------------------------------------
{
  echo "# Lean 4 and Idris 2 comparison programs: observed outcomes"
  echo
  echo "Generated by \`case_studies/comparison/run_lean_idris.sh\` on $(date -u '+%Y-%m-%d %H:%M UTC')."
  echo "Do not edit by hand; rerun the script."
  echo
  echo "## Tools"
  echo
  echo "- lean: \`$LEAN_V\`"
  echo "- lake: \`$LAKE_V\` (native builds use the toolchain pin \`$LEAN_TOOLCHAIN\`)"
  echo "- elan: \`$ELAN_V\`"
  echo "- idris2: \`$IDRIS_V\` (Chez Scheme back end; \`chez --version\`: \`$CHEZ_V\`)"
  echo "- Idris 2 packages in \`idris2 --libdir\`: \`$IDRIS_PKGS\`"
  echo "- OS: \`$OS_V\`"
  echo "- Lean programs are checked with \`lean FILE\`; accepted programs with a \`main\` are built with"
  echo "  \`lake build\` (a package in the build directory whose sources are \`lean/\`) and run."
  echo "- Idris 2 programs with a \`main\` are compiled with"
  echo "  \`idris2 -p linear -p contrib --dumpcases CASES -o NAME FILE\` and run; programs without \`main\`"
  echo "  are checked with \`idris2 -p linear -p contrib --check FILE\`."
  echo
  echo "## Legend"
  echo
  echo "- **Kind**: positive = a correct program (should be accepted); negative = the property is violated (should"
  echo "  be rejected before running; Expected is our prediction, ACCEPT or RUNTIME_ERROR where the tool cannot reject"
  echo "  it, as in the Rust/Racket and LRL tables); limit = probes whether the tool can express or enforce the property"
  echo "  at all (Expected is our prediction)."
  echo "- **Observed**: ACCEPT = compiled (and, if the file has \`main\`, ran with exit status 0); COMPILE_ERROR ="
  echo "  rejected before running (Lean elaboration or type error; Idris 2 type, linearity or coverage error);"
  echo "  RUNTIME_ERROR = compiled, then failed when run."
  echo "- **Program (variant)**: \`[IR: f, g]\` rows show the Lean compiler's final IR of the named definitions"
  echo "  (\`set_option trace.compiler.ir.result true\` in the file; \`◾\` marks an erased argument);"
  echo "  \`[--dumpcases: f, g]\` rows show the Idris 2 compiled case trees of the named definitions (the list"
  echo "  after \`=\` holds the run-time arguments; \`{arg:k}\` is the k-th source argument, counting implicits);"
  echo "  \`[Chez Scheme: f]\` checks the generated Scheme definition \`f\` for \`vector-set!\`."
  echo "  Such rows reuse the compilation of the same program in its \`build\` row; \"selected lines\" means"
  echo "  that the excerpt keeps the first line of the block and the lines relevant to the property."
  echo "- **Match**: Observed = Expected."
  echo "- **Excerpt**: first error message and location for compile errors; program output otherwise;"
  echo "  the intermediate code for \`[IR]\`, \`[--dumpcases]\` and \`[Chez Scheme]\` rows (cut to 300 characters;"
  echo "  the full blocks are below the table)."
  echo
  echo "## Results ($n_match of $n cases match the expected outcome)"
  echo
  echo "| Q | Property | Lang | Program (variant) | Kind | Expected | Observed | Match | Excerpt |"
  echo "|---|---|---|---|---|---|---|---|---|"
  printf '%s' "$ROWS"
  echo
  echo "## Compiler intermediate output (full blocks)"
  echo
  printf '%s\n' "$CASES" | while IFS='|' read -r lang q prop file kind expected mode arg; do
    [ "$mode" = ir ] || continue
    b="$(base_of "$file")"
    echo "### $q, \`$lang/$file\`: $(ir_names "$arg" | sed 's/ /, /g')"
    echo
    echo '```'
    for nm in $(ir_names "$arg"); do
      if [ "$lang" = lean ]; then lean_ir_block "$LOGS/lean_$b.check.txt" "$nm"
      else idris_case_tree "$IBUILD/$b/cases.txt" "$nm"; fi
    done
    echo '```'
    echo
  done
  echo "Full compiler and program output for every case is written to \`\$CMP_BUILD_DIR/logs/\` (not part of the repository)."
} >"$OUT"

echo
echo "wrote $OUT ($n_match/$n cases as expected); logs in $LOGS"
