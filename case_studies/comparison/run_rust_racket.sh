#!/usr/bin/env bash
# Rerun every Rust and Racket comparison program and write results_rust_racket.md.
#
# Usage:  case_studies/comparison/run_rust_racket.sh
# Env:    CMP_BUILD_DIR  directory for build outputs (default: a fresh mktemp directory).
#                        Nothing is written inside the repository except results_rust_racket.md.
#
# Each case is compiled and, if compilation succeeds, run. The observed outcome is one of
#   ACCEPT         compiled (or, for MODE=check / MODE=ir, passed that build step) and ran with exit 0
#   COMPILE_ERROR  rejected before running (rustc error; Racket expansion, Typed Racket, Cur or
#                  Turnstile type error)
#   RUNTIME_ERROR  compiled, then failed when run (non-zero exit status)
#   SKIPPED        a needed Racket package (typed-racket, cur, turnstile-example) is not installed
# Needs: rustc (tested with 1.78), Racket (tested with 9.3) with the packages typed-racket, cur and
# turnstile-example (`raco pkg install --auto typed-racket cur turnstile-example`).
# Compatible with the macOS system bash (3.2).
# Racket files are copied to the build directory and compiled there with `raco make`, so that
# `compiled/` directories are not created in the repository.

set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
BUILD="${CMP_BUILD_DIR:-$(mktemp -d "${TMPDIR:-/tmp}/lrl_cmp.XXXXXX")}"
OUT="$HERE/results_rust_racket.md"
RUST_SRC="$HERE/rust"
RKT_SRC="$HERE/racket"
RUST_BUILD="$BUILD/rust"
RKT_BUILD="$BUILD/racket"
LOGS="$BUILD/logs"
mkdir -p "$RUST_BUILD" "$RKT_BUILD" "$LOGS"

# ---------------------------------------------------------------------------------------------
# Cases: lang | Q | file | variant (rustc --cfg, "-" for none) | kind | expected | mode
#   kind:      positive = a correct program that uses the feature (ideally: accepted and runs);
#              negative = the property is violated (ideally: rejected before running).
#   expected:  our prediction of the observed outcome (ACCEPT, COMPILE_ERROR, RUNTIME_ERROR).
#              A positive predicted COMPILE_ERROR means "the tool cannot express this";
#              a negative predicted RUNTIME_ERROR / ACCEPT means "caught only at run time / not caught".
#   mode:      build (compile, then run), check (rustc --emit=metadata only, like `cargo check`),
#              ir (rustc --emit=llvm-ir; report the `define` line of div_with_proof)
# Racket files are run with `racket FILE`, which also runs a `main` submodule if there is one.
# ---------------------------------------------------------------------------------------------
CASES=$(cat <<'EOF'
rust|Q1|q01_head_const_generics.rs|-|positive|ACCEPT|build
rust|Q1|q01_head_const_generics.rs|empty|negative|COMPILE_ERROR|build
rust|Q1|q01_head_const_generics.rs|empty|negative|ACCEPT|check
rust|Q1|q01_head_const_generics.rs|plain_empty|negative|RUNTIME_ERROR|build
rust|Q1|q01_head_const_generics.rs|succ_type|positive|COMPILE_ERROR|build
rust|Q1|q01_head_typelevel.rs|-|positive|ACCEPT|build
rust|Q1|q01_head_typelevel.rs|empty|negative|COMPILE_ERROR|build
rust|Q2|q02_append_const_generics.rs|-|positive|COMPILE_ERROR|build
rust|Q2|q02_append_typelevel.rs|-|positive|ACCEPT|build
rust|Q2|q02_append_typelevel.rs|wrong_len|negative|COMPILE_ERROR|build
rust|Q2|q02_append_typelevel.rs|drop_elem|negative|COMPILE_ERROR|build
rust|Q3|q03_reverse_involution.rs|-|positive|ACCEPT|build
rust|Q3|q03_reverse_involution.rs|buggy|negative|RUNTIME_ERROR|build
rust|Q4|q04_zero_sized_proofs.rs|-|positive|ACCEPT|build
rust|Q4|q04_zero_sized_proofs.rs|-|positive|ACCEPT|ir
rust|Q4|q04_zero_sized_proofs.rs|forge|negative|COMPILE_ERROR|build
rust|Q4|q04_zero_sized_proofs.rs|zero_divisor|negative|RUNTIME_ERROR|build
rust|Q4|q04_zero_sized_proofs.rs|index_at_runtime|negative|COMPILE_ERROR|build
rust|Q5|q05_single_use_channel.rs|-|positive|ACCEPT|build
rust|Q5|q05_single_use_channel.rs|reuse|negative|COMPILE_ERROR|build
rust|Q6|q06_typestate.rs|-|positive|ACCEPT|build
rust|Q6|q06_typestate.rs|send_after_close|negative|COMPILE_ERROR|build
rust|Q6|q06_typestate.rs|close_twice|negative|COMPILE_ERROR|build
rust|Q7|q07_protocol_length.rs|-|positive|ACCEPT|build
rust|Q7|q07_protocol_length.rs|too_many|negative|COMPILE_ERROR|build
rust|Q7|q07_protocol_length.rs|too_few|negative|COMPILE_ERROR|build
rust|Q7|q07_protocol_length.rs|len_mismatch|negative|COMPILE_ERROR|build
rust|Q7|q07_protocol_length.rs|skip_send|negative|COMPILE_ERROR|build
rust|Q7|q07_protocol_length.rs|abandon|negative|ACCEPT|build
rust|Q7|q07_protocol_const_generics.rs|-|positive|COMPILE_ERROR|build
rust|Q8|q08_macro_hygiene.rs|-|positive|ACCEPT|build
rust|Q8|q08_macro_hygiene.rs|mix_units|negative|COMPILE_ERROR|build
rust|Q8|q08_macro_global_names.rs|-|positive|ACCEPT|build
rust|Q9|q09_two_mut_refs.rs|-|positive|ACCEPT|build
rust|Q9|q09_two_mut_refs.rs|alias_call|negative|COMPILE_ERROR|build
rust|Q9|q09_two_mut_refs.rs|alias_live|negative|COMPILE_ERROR|build
rust|Q10|q10_consume_both_branches.rs|-|positive|ACCEPT|build
rust|Q10|q10_consume_both_branches.rs|one_branch|positive|ACCEPT|build
rust|Q10|q10_consume_both_branches.rs|use_after|negative|COMPILE_ERROR|build
rust|Q11|q11_inplace_reverse.rs|-|positive|ACCEPT|build
rust|Q11|q11_inplace_reverse.rs|shared_alias|negative|COMPILE_ERROR|build
rust|Q11|q11_inplace_reverse.rs|use_after_move|negative|COMPILE_ERROR|build
rust|Q12|q12_fnonce_twice.rs|-|positive|ACCEPT|build
rust|Q12|q12_fnonce_twice.rs|call_twice|negative|COMPILE_ERROR|build
rust|Q12|q12_fnonce_twice.rs|as_fn|negative|COMPILE_ERROR|build
rust|Q12|q12_fnonce_twice.rs|in_loop|negative|COMPILE_ERROR|build
racket|Q1|q01_head_plain.rkt|-|positive|ACCEPT|build
racket|Q1|q01_head_plain__empty.rkt|-|negative|RUNTIME_ERROR|build
racket|Q1|q01_head_typed.rkt|-|positive|ACCEPT|build
racket|Q1|q01_head_typed__empty.rkt|-|negative|COMPILE_ERROR|build
racket|Q1|q01_head_refined.rkt|-|positive|ACCEPT|build
racket|Q1|q01_head_refined__empty.rkt|-|negative|COMPILE_ERROR|build
racket|Q1|q01_head_refined__unrefined.rkt|-|negative|ACCEPT|build
racket|Q1|q01_head_refined__submodule.rkt|-|positive|COMPILE_ERROR|build
racket|Q1|q01_head_cur.rkt|-|positive|ACCEPT|build
racket|Q1|q01_head_cur__empty.rkt|-|negative|COMPILE_ERROR|build
racket|Q1|q01_head_cur__any_length.rkt|-|negative|COMPILE_ERROR|build
racket|Q2|q02_append_plain.rkt|-|positive|ACCEPT|build
racket|Q2|q02_append_plain__off_by_one.rkt|-|negative|RUNTIME_ERROR|build
racket|Q2|q02_append_typed.rkt|-|positive|COMPILE_ERROR|build
racket|Q2|q02_append_refined.rkt|-|positive|ACCEPT|build
racket|Q2|q02_append_refined__wrong_len.rkt|-|negative|COMPILE_ERROR|build
racket|Q2|q02_append_refined__off_by_one.rkt|-|negative|COMPILE_ERROR|build
racket|Q2|q02_append_refined__vector_append.rkt|-|positive|COMPILE_ERROR|build
racket|Q2|q02_append_cur.rkt|-|positive|ACCEPT|build
racket|Q2|q02_append_cur__wrong_len.rkt|-|negative|COMPILE_ERROR|build
racket|Q2|q02_append_cur__drop_elem.rkt|-|negative|COMPILE_ERROR|build
racket|Q3|q03_reverse_involution_plain.rkt|-|positive|ACCEPT|build
racket|Q3|q03_reverse_involution_plain__buggy.rkt|-|negative|RUNTIME_ERROR|build
racket|Q3|q03_reverse_involution_refined.rkt|-|positive|COMPILE_ERROR|build
racket|Q3|q03_reverse_involution_cur.rkt|-|positive|ACCEPT|build
racket|Q3|q03_reverse_involution_cur__buggy.rkt|-|negative|COMPILE_ERROR|build
racket|Q4|q04_evidence_tokens_typed.rkt|-|positive|RUNTIME_ERROR|build
racket|Q4|q04_evidence_tokens_typed__forge.rkt|-|negative|COMPILE_ERROR|build
racket|Q5|q05_single_use_channel_plain.rkt|-|positive|ACCEPT|build
racket|Q5|q05_single_use_channel_plain__reuse.rkt|-|negative|RUNTIME_ERROR|build
racket|Q5|q05_single_use_channel_typed.rkt|-|positive|ACCEPT|build
racket|Q5|q05_single_use_channel_typed__reuse.rkt|-|negative|RUNTIME_ERROR|build
racket|Q5|q05_single_use_channel_lin.rkt|-|positive|ACCEPT|build
racket|Q5|q05_single_use_channel_lin__reuse.rkt|-|negative|COMPILE_ERROR|build
racket|Q6|q06_typestate_plain.rkt|-|positive|ACCEPT|build
racket|Q6|q06_typestate_plain__send_after_close.rkt|-|negative|RUNTIME_ERROR|build
racket|Q6|q06_typestate_typed.rkt|-|positive|ACCEPT|build
racket|Q6|q06_typestate_typed__send_after_close.rkt|-|negative|COMPILE_ERROR|build
racket|Q7|q07_protocol_length_plain.rkt|-|positive|ACCEPT|build
racket|Q7|q07_protocol_length_plain__too_many.rkt|-|negative|RUNTIME_ERROR|build
racket|Q7|q07_protocol_length_typed.rkt|-|positive|ACCEPT|build
racket|Q7|q07_protocol_length_typed__too_many.rkt|-|negative|COMPILE_ERROR|build
racket|Q7|q07_protocol_length_typed__too_few.rkt|-|negative|COMPILE_ERROR|build
racket|Q7|q07_protocol_length_typed__send_all.rkt|-|positive|COMPILE_ERROR|build
racket|Q8|q08_macro_hygiene.rkt|-|positive|ACCEPT|build
racket|Q8|q08_macro_plain_ops.rkt|-|positive|ACCEPT|build
racket|Q8|q08_macro_plain_ops__mix_units.rkt|-|negative|RUNTIME_ERROR|build
racket|Q8|q08_macro_typed_ops.rkt|-|positive|ACCEPT|build
racket|Q8|q08_macro_typed_ops__mix_units.rkt|-|negative|COMPILE_ERROR|build
racket|Q9|q09_distinct_boxes.rkt|-|positive|ACCEPT|build
racket|Q9|q09_aliasing_boxes.rkt|-|negative|ACCEPT|build
racket|Q9|q09_distinct_boxes_typed.rkt|-|positive|ACCEPT|build
racket|Q9|q09_aliasing_boxes_typed.rkt|-|negative|ACCEPT|build
racket|Q10|q10_consume_both_branches_plain.rkt|-|positive|ACCEPT|build
racket|Q10|q10_consume_both_branches_plain__use_after.rkt|-|negative|RUNTIME_ERROR|build
racket|Q10|q10_consume_both_branches_lin.rkt|-|positive|ACCEPT|build
racket|Q10|q10_consume_both_branches_lin__one_branch.rkt|-|positive|COMPILE_ERROR|build
racket|Q10|q10_consume_both_branches_lin__drop.rkt|-|positive|ACCEPT|build
racket|Q10|q10_consume_both_branches_lin__use_after.rkt|-|negative|COMPILE_ERROR|build
racket|Q11|q11_inplace_vector_reverse.rkt|-|positive|ACCEPT|build
racket|Q11|q11_inplace_vector_reverse__alias.rkt|-|negative|ACCEPT|build
racket|Q12|q12_once_closure_plain.rkt|-|positive|ACCEPT|build
racket|Q12|q12_once_closure_plain__call_twice.rkt|-|negative|RUNTIME_ERROR|build
racket|Q12|q12_once_closure_typed.rkt|-|positive|ACCEPT|build
racket|Q12|q12_once_closure_typed__call_twice.rkt|-|negative|RUNTIME_ERROR|build
racket|Q12|q12_once_closure_lin.rkt|-|positive|ACCEPT|build
racket|Q12|q12_once_closure_lin__call_twice.rkt|-|negative|COMPILE_ERROR|build
racket|Q12|q12_once_closure_lin__unrestricted_capture.rkt|-|negative|COMPILE_ERROR|build
EOF
)

prop_text() {
  case "$1" in
    Q1)  echo "indexed vector, total head" ;;
    Q2)  echo "append, length = sum" ;;
    Q3)  echo "proof: reverse is an involution" ;;
    Q4)  echo "proofs/evidence absent at run time" ;;
    Q5)  echo "single-use channel" ;;
    Q6)  echo "wrong protocol state rejected" ;;
    Q7)  echo "protocol length = data length" ;;
    Q8)  echo "hygienic macro generating typed ops" ;;
    Q9)  echo "two live mutable references to one location" ;;
    Q10) echo "value consumed in both branches" ;;
    Q11) echo "in-place update" ;;
    Q12) echo "once-only closure called twice" ;;
    *)   echo "$1" ;;
  esac
}

# Dialect of a case: rustc for Rust; for Racket, from the file's #lang line.
dialect_of() {
  local lang="$1" file="$2" first
  if [ "$lang" = rust ]; then echo "rustc"; return; fi
  first="$(head -n 1 "$RKT_SRC/$file")"
  case "$first" in
    *with-refinements*)            echo "Typed Racket + refinements" ;;
    "#lang typed/racket"*)         echo "Typed Racket" ;;
    "#lang cur"*)                  echo "Cur" ;;
    *turnstile/examples/linear*)   echo "Turnstile lin" ;;
    "#lang racket"*)               echo "Racket" ;;
    *)                             echo "Racket (other)" ;;
  esac
}

verdict_of() {
  case "$1:$2" in
    positive:ACCEPT)         echo "accepted" ;;
    positive:COMPILE_ERROR)  echo "rejected before running" ;;
    positive:RUNTIME_ERROR)  echo "failed at run time" ;;
    negative:ACCEPT)         echo "not detected" ;;
    negative:COMPILE_ERROR)  echo "rejected before running" ;;
    negative:RUNTIME_ERROR)  echo "detected at run time" ;;
    *)                       echo "skipped" ;;
  esac
}

# ---------------------------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------------------------
md_escape() {
  # one line, no pipes or backticks, build paths shortened, at most 260 characters
  tr '\n' ' ' | sed -e 's/|/\\|/g' -e 's/`/'"'"'/g' -e "s#$BUILD#<build>#g" -e 's/  */ /g' \
    | cut -c1-260
}

first_error_rust() {
  # first `error...` line and the following ` --> file:line:col` location
  awk '/^error/ && !e {e=$0; next} e && /-->/ && !l {l=$0; sub(/^ +/, "", l)} END {print e; if (l) print l}' "$1"
}

first_lines() {
  # first N non-empty lines, dropping Racket context/location headers, indented stack-trace
  # lines (paths) and Rust backtrace notes
  grep -v '^[[:space:]]*$' "$1" \
    | grep -v -E 'context\.\.\.:|^ *location\.\.\.:|^ *parsing context:|RUST_BACKTRACE' \
    | grep -v -E '^ +(body of|\.\.\.|/|<)' | head -n "$2"
}

racket_has() {
  # $@ = collection path components ending in a file name, e.g. typed racket base.rkt
  local file="${@: -1}" dirs=("${@:1:$#-1}") quoted=""
  for d in "${dirs[@]}"; do quoted="$quoted \"$d\""; done
  racket -l racket/base -e "(void (collection-file-path \"$file\"$quoted))" >/dev/null 2>&1
}

rust_case() {
  local file="$1" variant="$2" mode="$3" tag="$4"
  local cfg=()
  if [ "$variant" != "-" ]; then cfg=(--cfg "$variant"); fi
  local bin="$RUST_BUILD/$tag" err="$LOGS/$tag.compile.txt" run="$LOGS/$tag.run.txt"
  : >"$run"
  case "$mode" in
    check)
      if (cd "$RUST_SRC" && rustc --edition 2021 ${cfg[@]+"${cfg[@]}"} --emit=metadata -o "$bin.rmeta" "$file") 2>"$err"; then
        OBS=ACCEPT; MSG="check-only build (--emit=metadata) succeeded"
      else
        OBS=COMPILE_ERROR; MSG="$(first_error_rust "$err")"
      fi ;;
    ir)
      if (cd "$RUST_SRC" && rustc --edition 2021 ${cfg[@]+"${cfg[@]}"} -C opt-level=0 --emit=llvm-ir -o "$bin.ll" "$file") 2>"$err"; then
        OBS=ACCEPT; MSG="LLVM IR (opt-level=0): $(grep -m1 'define.*@div_with_proof' "$bin.ll" | sed 's/ *{$//')"
      else
        OBS=COMPILE_ERROR; MSG="$(first_error_rust "$err")"
      fi ;;
    build)
      if (cd "$RUST_SRC" && rustc --edition 2021 ${cfg[@]+"${cfg[@]}"} -o "$bin" "$file") 2>"$err"; then
        if "$bin" >"$run" 2>&1; then
          OBS=ACCEPT; MSG="$(first_lines "$run" 4)"
        else
          OBS=RUNTIME_ERROR; MSG="$(first_lines "$run" 4)"
        fi
      else
        OBS=COMPILE_ERROR; MSG="$(first_error_rust "$err")"
      fi ;;
  esac
}

racket_case() {
  local file="$1" tag="$2"
  local err="$LOGS/$tag.compile.txt" run="$LOGS/$tag.run.txt"
  : >"$run"
  if (cd "$RKT_BUILD" && raco make "$file") 2>"$err"; then
    if (cd "$RKT_BUILD" && racket "$file") >"$run" 2>&1; then
      OBS=ACCEPT; MSG="$(first_lines "$run" 4)"
    else
      OBS=RUNTIME_ERROR; MSG="$(first_lines "$run" 4)"
    fi
  else
    OBS=COMPILE_ERROR; MSG="$(first_lines "$err" 5)"
  fi
}

# ---------------------------------------------------------------------------------------------
# tool versions
# ---------------------------------------------------------------------------------------------
RUSTC_V="$(rustc --version --verbose 2>&1 | tr '\n' ';' | sed 's/;$//')"
CARGO_V="$(cargo --version 2>&1)"
RACKET_V="$(racket --version 2>&1)"
OS_V="$(uname -srm 2>&1)"
if command -v sw_vers >/dev/null 2>&1; then OS_V="$OS_V; macOS $(sw_vers -productVersion)"; fi
# `raco pkg show -a` marks automatically installed packages with a trailing `*`
PKGS_V="$(raco pkg show -a 2>/dev/null \
  | grep -E '^ *(typed-racket|typed-racket-lib|cur|cur-lib|turnstile-lib|turnstile-example|macrotypes-lib)\*? ' \
  | awk '{print $1" "$2}' | tr '\n' ';' | sed 's/;$//')"

HAVE_TR=0; racket_has typed racket base.rkt && HAVE_TR=1
HAVE_CUR=0; racket_has cur main.rkt && HAVE_CUR=1
HAVE_TURNSTILE=0; racket_has turnstile examples linear lin.rkt && HAVE_TURNSTILE=1

# copy Racket sources (excluding macOS AppleDouble files) to the build directory
find "$RKT_SRC" -maxdepth 1 -name '*.rkt' -not -name '._*' -exec cp {} "$RKT_BUILD/" \;

# ---------------------------------------------------------------------------------------------
# run
# ---------------------------------------------------------------------------------------------
ROWS=""
SUMMARY_DATA="$LOGS/summary_data.txt"
: >"$SUMMARY_DATA"
n=0; n_match=0
while IFS='|' read -r lang q file variant kind expected mode; do
  [ -z "$lang" ] && continue
  n=$((n + 1))
  prop="$(prop_text "$q")"
  dialect="$(dialect_of "$lang" "$file")"
  tag="$(printf '%03d' "$n")_${file%.*}"
  [ "$variant" != "-" ] && tag="${tag}__${variant}"
  [ "$mode" != "build" ] && tag="${tag}__${mode}"
  OBS=""; MSG=""
  if [ "$lang" = "rust" ]; then
    rust_case "$file" "$variant" "$mode" "$tag"
  else
    case "$dialect" in
      "Typed Racket"*) need=$HAVE_TR;        missing="typed-racket" ;;
      "Cur")           need=$HAVE_CUR;       missing="cur" ;;
      "Turnstile lin") need=$HAVE_TURNSTILE; missing="turnstile-example" ;;
      *)               need=1;               missing="" ;;
    esac
    if [ "$need" = 0 ]; then
      OBS=SKIPPED; MSG="$missing is not installed"
    else
      racket_case "$file" "$tag"
    fi
  fi
  if [ "$OBS" = "$expected" ]; then m=yes; n_match=$((n_match + 1)); else m=NO; fi
  verdict="$(verdict_of "$kind" "$OBS")"
  prog="$lang/$file"
  [ "$variant" != "-" ] && prog="$prog (--cfg $variant)"
  [ "$mode" = "check" ] && prog="$prog [--emit=metadata]"
  [ "$mode" = "ir" ] && prog="$prog [--emit=llvm-ir]"
  msg_md="$(printf '%s' "$MSG" | md_escape)"
  ROWS="$ROWS| $q | $dialect | \`$prog\` | $kind | $expected | $OBS | $m | $verdict | $msg_md |
"
  printf '%s|%s|%s|%s|%s\n' "$q" "$prop" "$dialect" "$kind" "$verdict" >>"$SUMMARY_DATA"
  printf '%-4s %-28s %-58s %-14s %-14s %s\n' "$q" "$dialect" "$file:$variant:$mode" "$expected" "$OBS" "$m"
done <<<"$CASES"

# One summary row per (property, dialect): the verdicts of its positive and negative programs.
summary_rows() {
  awk -F'|' '
    BEGIN {
      nv["positive"] = split("accepted|rejected before running|failed at run time|skipped", vp, "|")
      for (i = 1; i <= nv["positive"]; i++) vlist["positive", i] = vp[i]
      nv["negative"] = split("rejected before running|detected at run time|not detected|skipped", vn, "|")
      for (i = 1; i <= nv["negative"]; i++) vlist["negative", i] = vn[i]
    }
    {
      key = $1 "|" $3
      if (!(key in seen)) { seen[key] = 1; order[++k] = key; prop[key] = $2 }
      cnt[key, $4, $5]++
    }
    function render(key, kind,    i, v, out) {
      out = ""
      for (i = 1; i <= nv[kind]; i++) {
        v = vlist[kind, i]
        if ((key, kind, v) in cnt) out = out (out == "" ? "" : ", ") cnt[key, kind, v] " " v
      }
      return out == "" ? "none" : out
    }
    END {
      for (i = 1; i <= k; i++) {
        key = order[i]; split(key, kp, "|")
        printf "| %s | %s | %s | %s | %s |\n", kp[1], prop[key], kp[2], render(key, "positive"), render(key, "negative")
      }
    }' "$SUMMARY_DATA"
}

# ---------------------------------------------------------------------------------------------
# report
# ---------------------------------------------------------------------------------------------
{
  echo "# Rust and Racket comparison programs: observed outcomes"
  echo
  echo "Generated by \`case_studies/comparison/run_rust_racket.sh\` on $(date -u '+%Y-%m-%d %H:%M UTC')."
  echo "Do not edit by hand; rerun the script. What each program does is described in \`rust/README.md\`"
  echo "and \`racket/README.md\`."
  echo
  echo "## Tools"
  echo
  echo "- rustc: \`$RUSTC_V\`"
  echo "- cargo: \`$CARGO_V\`"
  echo "- racket: \`$RACKET_V\`"
  echo "- Racket packages (name, checksum): \`${PKGS_V:-none of typed-racket/cur/turnstile listed}\`"
  echo "- Typed Racket available: $HAVE_TR; Cur available: $HAVE_CUR; Turnstile examples available: $HAVE_TURNSTILE"
  echo "- OS: \`$OS_V\`"
  echo "- Rust programs are compiled with \`rustc --edition 2021 [--cfg VARIANT] -o BIN FILE\` (debug, opt-level 0) and run."
  echo "- Racket programs are copied to the build directory, compiled with \`raco make FILE\`, then run with \`racket FILE\`"
  echo "  (which also runs the \`main\` submodule). Cur and Turnstile programs print the values of their top-level"
  echo "  expressions when run."
  echo
  echo "## Legend"
  echo
  echo "- **Dialect**: rustc (stable Rust, no external crates or verifiers); Racket (\`#lang racket/base\`); Typed Racket"
  echo "  (\`#lang typed/racket\`); Typed Racket + refinements (\`#lang typed/racket #:with-refinements\`, experimental);"
  echo "  Cur (\`#lang cur\`, a dependently typed language implemented with Turnstile+ macros); Turnstile lin"
  echo "  (\`#lang s-exp turnstile/examples/linear/lin\` or \`lin+chan\`, the linear-types example language of the"
  echo "  turnstile-example package)."
  echo "- **Kind**: positive = a correct program that uses the feature (ideally accepted and run); negative = the property"
  echo "  is violated (ideally rejected before running)."
  echo "- **Expected**: our prediction. A positive predicted COMPILE_ERROR means the tool cannot express the program;"
  echo "  a negative predicted RUNTIME_ERROR or ACCEPT means the violation is caught only at run time, or not at all."
  echo "- **Observed**: ACCEPT = compiled (for \`--emit=metadata\` / \`--emit=llvm-ir\`: passed that build step) and ran with"
  echo "  exit status 0; COMPILE_ERROR = rejected before running (rustc error; Racket expansion, Typed Racket, Cur or"
  echo "  Turnstile type error); RUNTIME_ERROR = compiled, then exited with a non-zero status; SKIPPED = package not installed."
  echo "- **Match**: Observed = Expected."
  echo "- **Verdict**: positive: accepted / rejected before running / failed at run time; negative: rejected before"
  echo "  running / detected at run time / not detected."
  echo "- **Excerpt**: first error line and location for compile errors; first lines of output otherwise."
  echo "- The Q4 programs check their own run-time representation and exit with an error when the evidence is present at"
  echo "  run time (Rust: \`size_of\` assertions; Typed Racket: the arity of the function that takes the evidence)."
  echo
  echo "## Summary by property and dialect"
  echo
  echo "| Q | Property | Dialect | Positive programs | Negative programs |"
  echo "|---|---|---|---|---|"
  summary_rows
  echo
  echo "## Results ($n_match of $n cases match the expected outcome)"
  echo
  echo "| Q | Dialect | Program (variant) | Kind | Expected | Observed | Match | Verdict | Excerpt |"
  echo "|---|---|---|---|---|---|---|---|---|"
  printf '%s' "$ROWS"
  echo
  echo "Full compiler and program output for every case is written to \`\$CMP_BUILD_DIR/logs/\` (not part of the repository)."
} >"$OUT"

echo
echo "wrote $OUT ($n_match/$n cases as expected); logs in $LOGS"
