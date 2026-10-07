#!/usr/bin/env bash
# Rerun every LRL comparison program and write results_lrl.md.
#
# Usage:  case_studies/comparison/run_lrl.sh
# Env:    LRL_BIN        the LRL CLI to use (default: build it with `cargo build -p cli` and use
#                        ${CARGO_TARGET_DIR:-<repo>/target}/debug/cli).
#         CMP_BUILD_DIR  directory for binaries and logs (default: a fresh mktemp directory).
#
# The CLI is run from the repository root (it finds stdlib/ relative to the working directory).
# Nothing is written inside the repository except results_lrl.md and the generated Rust files
# that `lrl compile` itself writes to the git-ignored build/ directory.
#
# Every case is compiled with `lrl compile FILE --backend B -o BIN` and, if that succeeds, BIN is
# run. The observed outcome is one of
#   ACCEPT         compiled (front end, kernel and MIR checks passed, rustc built the generated
#                  Rust) and the binary exited with status 0
#   COMPILE_ERROR  rejected by LRL before code generation (elaborator F..., kernel K..., MIR M...)
#   BACKEND_ERROR  LRL's checks passed, but rustc rejected the generated Rust (a code generator
#                  bug or limitation, not a type or ownership error)
#   RUNTIME_ERROR  compiled, then the binary exited with a non-zero status
#   CRASH          the LRL compiler itself crashed (e.g. stack overflow)
# Modes other than `build` inspect the generated Rust or the stdlib (see rust_evidence); the
# `limit` rows among them record what LRL cannot do (Q9, Q11) as an observed outcome:
#   NOT_IN_PLACE         the generated cons constructor allocates a new cell (no in-place update)
#   NO_OPERATION_ON_REF  no stdlib declaration takes a `Ref` argument: a reference can be created
#                        and passed, but nothing reads or writes through it
# Compatible with the macOS system bash (3.2).

set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
BUILD="${CMP_BUILD_DIR:-$(mktemp -d "${TMPDIR:-/tmp}/lrl_cmp.XXXXXX")}"
OUT="$HERE/results_lrl.md"
SRC="$HERE/lrl"
BIN_DIR="$BUILD/lrl_bin"
LOGS="$BUILD/lrl_logs"
mkdir -p "$BIN_DIR" "$LOGS"

if [ -z "${LRL_BIN:-}" ]; then
  echo "LRL_BIN not set: building the CLI with cargo build -p cli" >&2
  (cd "$REPO" && cargo build -q -p cli) || { echo "cargo build failed" >&2; exit 1; }
  LRL_BIN="${CARGO_TARGET_DIR:-$REPO/target}/debug/cli"
fi
[ -x "$LRL_BIN" ] || { echo "LRL CLI not found: $LRL_BIN" >&2; exit 1; }

# ---------------------------------------------------------------------------------------------
# Cases: Q | file | backend (typed, dynamic) | kind | expected | mode
#   kind:      positive = a correct program that uses the feature (ideally: accepted and runs);
#              negative = the property is violated (ideally: rejected before running);
#              limit = an evidence row probing what LRL can express at all (see the modes).
#   expected:  our prediction of the observed outcome. A positive predicted COMPILE_ERROR means
#              "LRL cannot express this"; a negative predicted ACCEPT means "not caught"; a
#              predicted BACKEND_ERROR is a known code-generator bug or limitation (README.md).
#   mode:      build (compile, then run) or one of the evidence modes:
#              rust_safe_div  (typed) the signature of the generated `fn safe_div`
#              rust_vec_enum  (typed) the generated `enum lrl_Vec`
#              rust_cons      (typed) the generated cons constructor and the List<Tok> recursor arm;
#                             NOT_IN_PLACE if the constructor allocates (`Rc::new`/`Box::new`)
#              rust_dyn_cons  (dynamic) the generated `fn cons`; NOT_IN_PLACE if it allocates
#              prelude_ref_ops the declarations of the stdlib files that mention `Ref`;
#                             NO_OPERATION_ON_REF if none of them takes a `Ref` argument
# ---------------------------------------------------------------------------------------------
CASES=$(cat <<'EOF'
Q1|q01_head.lrl|dynamic|positive|ACCEPT|build
Q1|q01_head.lrl|typed|positive|ACCEPT|build
Q1|q01_head__empty.lrl|dynamic|negative|COMPILE_ERROR|build
Q1|q01_head__empty.lrl|typed|negative|COMPILE_ERROR|build
Q1|q01_head__any_length.lrl|dynamic|negative|COMPILE_ERROR|build
Q1|q01_head__any_length.lrl|typed|negative|COMPILE_ERROR|build
Q2|q02_append.lrl|dynamic|positive|ACCEPT|build
Q2|q02_append.lrl|typed|positive|ACCEPT|build
Q2|q02_append__wrong_len.lrl|dynamic|negative|COMPILE_ERROR|build
Q2|q02_append__wrong_len.lrl|typed|negative|COMPILE_ERROR|build
Q2|q02_append__drop_elem.lrl|dynamic|negative|COMPILE_ERROR|build
Q2|q02_append__drop_elem.lrl|typed|negative|COMPILE_ERROR|build
Q3|q03_reverse_involution.lrl|dynamic|positive|ACCEPT|build
Q3|q03_reverse_involution.lrl|typed|positive|ACCEPT|build
Q3|q03_reverse_involution__buggy.lrl|dynamic|negative|COMPILE_ERROR|build
Q3|q03_reverse_involution__buggy.lrl|typed|negative|COMPILE_ERROR|build
Q3|q03_reverse_involution__false_law.lrl|dynamic|negative|COMPILE_ERROR|build
Q3|q03_reverse_involution__false_law.lrl|typed|negative|COMPILE_ERROR|build
Q4|q04_erasure.lrl|dynamic|positive|ACCEPT|build
Q4|q04_erasure.lrl|typed|positive|ACCEPT|build
Q4|q04_erasure.lrl|typed|positive|ACCEPT|rust_safe_div
Q4|q04_erasure.lrl|typed|positive|ACCEPT|rust_vec_enum
Q4|q04_erasure__zero_divisor.lrl|dynamic|negative|COMPILE_ERROR|build
Q4|q04_erasure__zero_divisor.lrl|typed|negative|COMPILE_ERROR|build
Q4|q04_erasure__forge.lrl|dynamic|negative|COMPILE_ERROR|build
Q4|q04_erasure__forge.lrl|typed|negative|COMPILE_ERROR|build
Q4|q04_erasure__index_at_runtime.lrl|dynamic|negative|ACCEPT|build
Q4|q04_erasure__index_at_runtime.lrl|typed|negative|ACCEPT|build
Q5|q05_single_use_channel.lrl|dynamic|positive|ACCEPT|build
Q5|q05_single_use_channel.lrl|typed|positive|ACCEPT|build
Q5|q05_single_use_channel__reuse.lrl|dynamic|negative|COMPILE_ERROR|build
Q5|q05_single_use_channel__reuse.lrl|typed|negative|COMPILE_ERROR|build
Q6|q06_typestate.lrl|dynamic|positive|ACCEPT|build
Q6|q06_typestate.lrl|typed|positive|ACCEPT|build
Q6|q06_typestate__send_after_close.lrl|dynamic|negative|COMPILE_ERROR|build
Q6|q06_typestate__send_after_close.lrl|typed|negative|COMPILE_ERROR|build
Q6|q06_typestate__close_twice.lrl|dynamic|negative|COMPILE_ERROR|build
Q6|q06_typestate__close_twice.lrl|typed|negative|COMPILE_ERROR|build
Q7|q07_protocol_length.lrl|dynamic|positive|ACCEPT|build
Q7|q07_protocol_length.lrl|typed|positive|ACCEPT|build
Q7|q07_protocol_length__too_many.lrl|dynamic|negative|COMPILE_ERROR|build
Q7|q07_protocol_length__too_many.lrl|typed|negative|COMPILE_ERROR|build
Q7|q07_protocol_length__too_few.lrl|dynamic|negative|COMPILE_ERROR|build
Q7|q07_protocol_length__too_few.lrl|typed|negative|COMPILE_ERROR|build
Q7|q07_protocol_length__len_mismatch.lrl|dynamic|negative|COMPILE_ERROR|build
Q7|q07_protocol_length__len_mismatch.lrl|typed|negative|COMPILE_ERROR|build
Q7|q07_protocol_length__skip_send.lrl|dynamic|negative|COMPILE_ERROR|build
Q7|q07_protocol_length__skip_send.lrl|typed|negative|COMPILE_ERROR|build
Q7|q07_protocol_length__abandon.lrl|dynamic|negative|ACCEPT|build
Q7|q07_protocol_length__abandon.lrl|typed|negative|ACCEPT|build
Q8|q08_macro_hygiene.lrl|dynamic|positive|ACCEPT|build
Q8|q08_macro_hygiene.lrl|typed|positive|ACCEPT|build
Q8|q08_macro_hygiene__mix_units.lrl|dynamic|negative|COMPILE_ERROR|build
Q8|q08_macro_hygiene__mix_units.lrl|typed|negative|COMPILE_ERROR|build
Q8|q08_macro_global_names.lrl|dynamic|positive|ACCEPT|build
Q8|q08_macro_global_names.lrl|typed|positive|ACCEPT|build
Q8|q08_macro_global_names__lib_only.lrl|dynamic|positive|COMPILE_ERROR|build
Q8|q08_macro_global_names__lib_only.lrl|typed|positive|COMPILE_ERROR|build
Q9|q09_two_mut_refs.lrl|dynamic|positive|ACCEPT|build
Q9|q09_two_mut_refs.lrl|typed|positive|ACCEPT|build
Q9|q09_two_mut_refs.lrl|dynamic|limit|NO_OPERATION_ON_REF|prelude_ref_ops
Q9|q09_two_mut_refs.lrl|typed|limit|NO_OPERATION_ON_REF|prelude_ref_ops
Q9|q09_two_mut_refs__alias_call.lrl|dynamic|negative|COMPILE_ERROR|build
Q9|q09_two_mut_refs__alias_call.lrl|typed|negative|COMPILE_ERROR|build
Q9|q09_two_mut_refs__alias_live.lrl|dynamic|negative|COMPILE_ERROR|build
Q9|q09_two_mut_refs__alias_live.lrl|typed|negative|COMPILE_ERROR|build
Q10|q10_consume_both_branches.lrl|dynamic|positive|ACCEPT|build
Q10|q10_consume_both_branches.lrl|typed|positive|ACCEPT|build
Q10|q10_consume_both_branches__one_branch.lrl|dynamic|positive|ACCEPT|build
Q10|q10_consume_both_branches__one_branch.lrl|typed|positive|ACCEPT|build
Q10|q10_consume_both_branches__use_after.lrl|dynamic|negative|COMPILE_ERROR|build
Q10|q10_consume_both_branches__use_after.lrl|typed|negative|COMPILE_ERROR|build
Q11|q11_inplace_reverse.lrl|dynamic|positive|ACCEPT|build
Q11|q11_inplace_reverse.lrl|typed|positive|ACCEPT|build
Q11|q11_inplace_reverse.lrl|dynamic|limit|NOT_IN_PLACE|rust_dyn_cons
Q11|q11_inplace_reverse.lrl|typed|limit|NOT_IN_PLACE|rust_cons
Q11|q11_inplace_reverse__use_after_move.lrl|dynamic|negative|COMPILE_ERROR|build
Q11|q11_inplace_reverse__use_after_move.lrl|typed|negative|COMPILE_ERROR|build
Q12|q12_fnonce_twice.lrl|dynamic|positive|ACCEPT|build
Q12|q12_fnonce_twice.lrl|typed|positive|ACCEPT|build
Q12|q12_fnonce_twice__call_twice.lrl|dynamic|negative|COMPILE_ERROR|build
Q12|q12_fnonce_twice__call_twice.lrl|typed|negative|COMPILE_ERROR|build
Q12|q12_fnonce_twice__as_fn.lrl|dynamic|negative|COMPILE_ERROR|build
Q12|q12_fnonce_twice__as_fn.lrl|typed|negative|COMPILE_ERROR|build
Q12|q12_fnonce_twice__in_loop.lrl|dynamic|negative|COMPILE_ERROR|build
Q12|q12_fnonce_twice__in_loop.lrl|typed|negative|COMPILE_ERROR|build
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

verdict_of() {
  case "$1:$2" in
    positive:ACCEPT)         echo "accepted" ;;
    positive:COMPILE_ERROR)  echo "rejected before running" ;;
    positive:BACKEND_ERROR)  echo "checks passed, code generation failed" ;;
    positive:RUNTIME_ERROR)  echo "failed at run time" ;;
    negative:ACCEPT)         echo "not detected" ;;
    negative:COMPILE_ERROR)  echo "rejected before running" ;;
    negative:BACKEND_ERROR)  echo "not detected by the checks, code generation failed" ;;
    negative:RUNTIME_ERROR)  echo "detected at run time" ;;
    limit:NOT_IN_PLACE)      echo "no in-place update (new cells are allocated)" ;;
    limit:NO_OPERATION_ON_REF) echo "no operation reads or writes through a reference" ;;
    limit:ACCEPT)            echo "accepted" ;;
    limit:COMPILE_ERROR)     echo "rejected before running" ;;
    limit:BACKEND_ERROR)     echo "checks passed, code generation failed" ;;
    limit:RUNTIME_ERROR)     echo "failed at run time" ;;
    *)                       echo "compiler crashed" ;;
  esac
}

# ---------------------------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------------------------
strip_ansi() { sed 's/\x1b\[[0-9;]*m//g'; }

md_escape() {
  # one line, no pipes or backticks, build paths shortened, at most 300 characters
  tr '\n' ' ' | sed -e 's/|/\\|/g' -e 's/`/'"'"'/g' -e "s#$BUILD#<build>#g" -e "s#$REPO/##g" \
    -e 's#build/output_[0-9_]*\.rs#<generated>.rs#g' -e 's/  */ /g' | cut -c1-300
}

first_lrl_error() {
  # first LRL diagnostic line ("Error: ...")
  grep -m1 -E '^Error' "$1"
}

first_rustc_error() {
  # first rustc error line, its location, and the first expected/found note
  awk '/^error/ && !e {e=$0; next}
       e && /-->/ && !l {l=$0; sub(/^ +/, "", l)}
       e && /expected .*found/ && !x {x=$0; sub(/^.*expected/, "expected", x)}
       END {printf "rustc (generated Rust): %s", e; if (l) printf " %s", l; if (x) printf " %s", x}' "$1"
}

first_lines() {
  grep -v '^[[:space:]]*$' "$1" | head -n "$2"
}

generated_rust() {
  # path of the generated Rust file named in the CLI output ("Compiling build/output_<tag>.rs ...")
  local rel
  rel="$(grep -m1 -o 'build/output_[0-9_]*\.rs' "$1")"
  [ -n "$rel" ] && echo "$REPO/$rel"
}

rust_evidence() {
  # $1 = mode, $2 = generated Rust file; prints the excerpt
  local mode="$1" rs="$2" line
  case "$mode" in
    rust_safe_div)
      line="$(grep -m1 '^fn safe_div' "$rs" | sed 's/ *{$//')"
      echo "typed backend: $line" ;;
    rust_vec_enum)
      line="$(grep -m1 -A3 '^enum lrl_Vec' "$rs" | tr '\n' ' ')"
      echo "typed backend: $line" ;;
    rust_cons)
      line="$(grep -m1 -A1 '^fn cons<' "$rs" | grep -o -E 'List::cons\(a1, (Box|Rc)::new\(a2\)\)' | head -n 1)"
      local recline
      # the first recursor over List<Tok>: its cons arm (up to the recursive call on the tail)
      recline="$(awk '/^fn rec_List_entry_[0-9]+_impl\(.*List<Tok>/ {f=$2; sub(/\(.*/, "", f); want=1; next}
                      want && /^fn / {want=0}
                      want && (i = index($0, "List::cons(field_0, field_1)")) {
                        rest = substr($0, i); j = index(rest, "field_1.clone());")
                        if (j) rest = substr(rest, 1, j + length("field_1.clone());") - 1)
                        print f ": " rest; exit }' "$rs")"
      echo "typed backend: fn cons builds $line; $recline" ;;
    rust_dyn_cons)
      line="$(grep -m1 '^fn cons()' "$rs" | grep -o -E '(Rc|Box)::new\(List::Cons\([A-Za-z0-9_.]*(\(\))?, [A-Za-z0-9_]+\)\)' | head -n 1)"
      echo "dynamic backend: fn cons builds Value::List($line)" ;;
    prelude_ref_ops)
      prelude_ref_ops ;;
  esac
}

# The observed outcome of an evidence row (see the modes above).
evidence_outcome() {
  # $1 = mode, $2 = excerpt
  case "$1" in
    rust_cons|rust_dyn_cons)
      if printf '%s' "$2" | grep -q -E '(Rc|Box)::new\((a2|List::Cons)'; then echo NOT_IN_PLACE; else echo ACCEPT; fi ;;
    prelude_ref_ops)
      if printf '%s' "$2" | grep -q 'taking a Ref argument: none'; then echo NO_OPERATION_ON_REF; else echo ACCEPT; fi ;;
    *) echo ACCEPT ;;
  esac
}

# Declarations (axiom/def/partial/unsafe/noncomputable/inductive) of every stdlib file that
# mention `Ref`, and those that take a `Ref` argument (a Pi binder whose domain is a `Ref`).
prelude_ref_ops() {
  python3 - "$REPO/stdlib" <<'REFEOF'
import os, re, sys
root = sys.argv[1]
files = []
for d, _, fs in os.walk(root):
    files += [os.path.join(d, f) for f in fs if f.endswith('.lrl') and not f.startswith('._')]
def forms(text):
    text = re.sub(r';[^\n]*', '', text)
    out, depth, cur = [], 0, ''
    for ch in text:
        if depth == 0 and ch != '(':
            continue
        cur += ch
        depth += (ch == '(') - (ch == ')')
        if depth == 0:
            out.append(' '.join(cur.split())); cur = ''
    return out
head = re.compile(r'\((axiom|def|partial|unsafe|noncomputable|inductive)\s+(?:\[[^\]]*\]\s+|\([^()]*\)\s+|copy\s+)*([^\s()]+)')
binder_ref = re.compile(r'\(pi\s+(?:#\[[^\]]*\]\s+|fn\s+|fnmut\s+|fnonce\s+)?(?:\{\s*)?[^\s(){}]+\s+\(Ref\b')
mention, taking = [], []
for f in sorted(files):
    for form in forms(open(f, encoding='utf-8').read()):
        m = head.match(form)
        if not m or not re.search(r'\bRef\b', form):
            continue
        mention.append(m.group(2))
        if binder_ref.search(form):
            taking.append(m.group(2))
print('stdlib declarations mentioning Ref: %s; taking a Ref argument: %s'
      % (', '.join(mention) or 'none', ', '.join(taking) or 'none'))
REFEOF
}

lrl_case() {
  local file="$1" backend="$2" mode="$3" tag="$4"
  local bin="$BIN_DIR/$tag" log="$LOGS/$tag.compile.txt" run="$LOGS/$tag.run.txt" status
  : >"$run"
  rm -f "$bin"
  (cd "$REPO" && "$LRL_BIN" compile "$SRC/$file" --backend "$backend" -o "$bin") 2>&1 | strip_ansi >"$log"
  status=${PIPESTATUS[0]}
  if [ "$status" -eq 0 ] && [ -x "$bin" ]; then
    if [ "$mode" = "build" ]; then
      if "$bin" >"$run" 2>&1; then
        OBS=ACCEPT; MSG="$(first_lines "$run" 8)"
      else
        OBS=RUNTIME_ERROR; MSG="$(first_lines "$run" 8)"
      fi
    else
      local rs
      rs="$(generated_rust "$log")"
      cp "$rs" "$LOGS/$tag.generated.rs" 2>/dev/null
      MSG="$(rust_evidence "$mode" "$rs")"; OBS="$(evidence_outcome "$mode" "$MSG")"
    fi
  elif [ "$status" -ge 128 ] || grep -q "has overflowed its stack" "$log"; then
    OBS=CRASH; MSG="exit status $status: $(grep -m1 -E 'overflowed|panicked|fatal' "$log")"
  elif grep -q '^error' "$log"; then
    OBS=BACKEND_ERROR; MSG="$(first_rustc_error "$log")"
  else
    OBS=COMPILE_ERROR; MSG="$(first_lrl_error "$log")"
    [ -z "$MSG" ] && MSG="$(first_lines "$log" 3)"
  fi
}

# ---------------------------------------------------------------------------------------------
# tool versions
# ---------------------------------------------------------------------------------------------
LRL_V="$("$LRL_BIN" --version 2>&1 | head -n 1)"
GIT_V="$(cd "$REPO" && git rev-parse --short HEAD 2>/dev/null)"
# Modified tracked files, not counting results files (which reruns of the scripts rewrite).
GIT_DIRTY="$(cd "$REPO" && git status --porcelain --untracked-files=no -- . ':!**/results_*.md' ':!**/SUMMARY.md' ':!bench/results' ':!paper' 2>/dev/null | grep -v '^error' | wc -l | tr -d ' ')"
LRL_SHA="$(shasum -a 256 "$LRL_BIN" 2>/dev/null | cut -c1-16)"
RUSTC_V="$(rustc --version 2>&1)"
OS_V="$(uname -srm 2>&1)"
if command -v sw_vers >/dev/null 2>&1; then OS_V="$OS_V; macOS $(sw_vers -productVersion)"; fi

# ---------------------------------------------------------------------------------------------
# run
# ---------------------------------------------------------------------------------------------
ROWS=""
SUMMARY_DATA="$LOGS/summary_data.txt"
: >"$SUMMARY_DATA"
n=0; n_match=0
while IFS='|' read -r q file backend kind expected mode; do
  [ -z "$q" ] && continue
  n=$((n + 1))
  prop="$(prop_text "$q")"
  dialect="LRL, $backend backend"
  tag="$(printf '%03d' "$n")_${file%.lrl}_${backend}"
  [ "$mode" != "build" ] && tag="${tag}__${mode}"
  OBS=""; MSG=""
  lrl_case "$file" "$backend" "$mode" "$tag"
  if [ "$OBS" = "$expected" ]; then m=yes; n_match=$((n_match + 1)); else m=NO; fi
  verdict="$(verdict_of "$kind" "$OBS")"
  prog="lrl/$file"
  case "$mode" in
    rust_safe_div) prog="$prog [generated Rust: fn safe_div]" ;;
    rust_vec_enum) prog="$prog [generated Rust: enum lrl_Vec]" ;;
    rust_cons)     prog="$prog [generated Rust: cons, List<Tok> recursor]" ;;
    rust_dyn_cons) prog="$prog [generated Rust: fn cons]" ;;
    prelude_ref_ops) prog="$prog [stdlib: declarations mentioning Ref]" ;;
  esac
  msg_md="$(printf '%s' "$MSG" | md_escape)"
  ROWS="$ROWS| $q | $dialect | \`$prog\` | $kind | $expected | $OBS | $m | $verdict | $msg_md |
"
  printf '%s|%s|%s|%s|%s\n' "$q" "$prop" "$dialect" "$kind" "$verdict" >>"$SUMMARY_DATA"
  printf '%-4s %-22s %-48s %-14s %-14s %s\n' "$q" "$dialect" "$file:$mode" "$expected" "$OBS" "$m"
done <<<"$CASES"

# One summary row per (property, dialect): the verdicts of its positive and negative programs.
summary_rows() {
  awk -F'|' '
    BEGIN {
      nv["positive"] = split("accepted|rejected before running|checks passed, code generation failed|failed at run time|compiler crashed", vp, "|")
      for (i = 1; i <= nv["positive"]; i++) vlist["positive", i] = vp[i]
      nv["negative"] = split("rejected before running|detected at run time|not detected|not detected by the checks, code generation failed|compiler crashed", vn, "|")
      for (i = 1; i <= nv["negative"]; i++) vlist["negative", i] = vn[i]
      nv["limit"] = split("no in-place update (new cells are allocated)|no operation reads or writes through a reference|accepted|rejected before running|checks passed, code generation failed|failed at run time|compiler crashed", vl, "|")
      for (i = 1; i <= nv["limit"]; i++) vlist["limit", i] = vl[i]
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
        pos = render(key, "positive"); lim = render(key, "limit")
        if (lim != "none") pos = pos "; limit probe: " lim
        printf "| %s | %s | %s | %s | %s |\n", kp[1], prop[key], kp[2], pos, render(key, "negative")
      }
    }' "$SUMMARY_DATA"
}

# ---------------------------------------------------------------------------------------------
# report
# ---------------------------------------------------------------------------------------------
{
  echo "# LRL comparison programs: observed outcomes"
  echo
  echo "Generated by \`case_studies/comparison/run_lrl.sh\` on $(date -u '+%Y-%m-%d %H:%M UTC')."
  echo "Do not edit by hand; rerun the script. What each program does is described in \`lrl/README.md\`."
  echo
  echo "## Tools"
  echo
  echo "- lrl: \`$LRL_V\` (CLI binary \`$(printf '%s' "$LRL_BIN" | sed "s#$REPO/##")\`, SHA-256 prefix \`$LRL_SHA\`;"
  echo "  built from the repository working tree at commit \`$GIT_V\`, with $GIT_DIRTY modified tracked file(s) other than results files)"
  echo "- rustc (used by \`lrl compile\` for the generated Rust): \`$RUSTC_V\`"
  echo "- OS: \`$OS_V\`"
  echo "- Every program is compiled from the repository root with"
  echo "  \`lrl compile FILE --backend {typed,dynamic} -o BIN\` (parse, macro expansion, elaboration, kernel check,"
  echo "  MIR typing / ownership / borrow check, Rust code generation, rustc) and BIN is run."
  echo
  echo "## Legend"
  echo
  echo "- **Dialect**: LRL with the typed backend (Rust with LRL types mapped to Rust types) or the dynamic backend"
  echo "  (Rust over a universal \`Value\` type). Both backends run the same checks before code generation; they differ"
  echo "  only in the generated code."
  echo "- **Kind**: positive = a correct program that uses the feature (ideally accepted and run); negative = the property"
  echo "  is violated (ideally rejected before running); limit = an evidence row probing what LRL can express at all."
  echo "- **Expected**: our prediction. A positive predicted COMPILE_ERROR means LRL cannot express the program;"
  echo "  a negative predicted ACCEPT means the violation is not caught; a predicted BACKEND_ERROR is a known"
  echo "  code-generator bug or limitation (listed in \`lrl/README.md\`)."
  echo "- **Observed**: ACCEPT = LRL's checks passed, rustc built the generated Rust, and the binary exited with status 0"
  echo "  (for \`[generated Rust: ...]\` rows: the build succeeded and the excerpt quotes the generated code);"
  echo "  COMPILE_ERROR = rejected by LRL before code generation (diagnostic codes: F = elaborator, K = kernel,"
  echo "  M = MIR); BACKEND_ERROR = LRL's checks passed but rustc rejected the generated Rust; RUNTIME_ERROR = compiled,"
  echo "  then exited with a non-zero status; CRASH = the LRL compiler crashed. Limit rows: NOT_IN_PLACE = the generated"
  echo "  cons constructor allocates a new cell (\`Rc::new\`/\`Box::new\`), i.e. there is no in-place update;"
  echo "  NO_OPERATION_ON_REF = no declaration of the stdlib files takes a \`Ref\` argument, i.e. nothing reads or writes"
  echo "  through a reference."
  echo "- **Match**: Observed = Expected."
  echo "- **Verdict**: positive: accepted / rejected before running / checks passed, code generation failed / failed at"
  echo "  run time; negative: rejected before running / detected at run time / not detected / not detected by the"
  echo "  checks, code generation failed; limit: no in-place update (new cells are allocated) / no operation reads or"
  echo "  writes through a reference."
  echo "- **Excerpt**: first LRL diagnostic (or first rustc error with its location) for rejected programs; the first"
  echo "  lines of output otherwise (each \`print_nat\` prints one line; the binary then prints \`Result: <value of main>\`)."
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
  echo "Full compiler and program output for every case is written to \`\$CMP_BUILD_DIR/lrl_logs/\` (not part of the repository)."
} >"$OUT"

echo
echo "wrote $OUT ($n_match/$n cases as expected); logs in $LOGS"
