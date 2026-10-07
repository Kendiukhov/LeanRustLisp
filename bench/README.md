# LRL measurements (`bench/`)

This directory holds the scripts, programs and raw results behind every performance-related
statement about LeanRustLisp (LRL) in the revised paper.

**LRL makes no performance claims beyond the measurements in `bench/results/`.** They describe one
machine, one compiler build and the programs in `bench/programs/`; they are not a benchmark suite
and do not support general statements about the speed of LRL programs, of either backend, or of
dependently typed code in general. Section "What these measurements do not show" lists what they
do not establish.

## Layout

| path | content |
|---|---|
| `run_bench.py` | the driver (Python 3, standard library only) |
| `programs/*.lrl` | LRL workload templates (`@SIZE@`, `@A@`, `@B@` are filled in by the driver) |
| `programs/rust_reference/vec_rev_sum.rs` | plain-Rust reference point (context only) |
| `results/{compile_time,runtime,proof_arg,rust_reference,indexcost}.csv` | raw data: one row per run, including warm-up runs (flagged `warmup=1`) |
| `results/batches.csv` | one row per measurement batch: `uptime`, busy processes, top CPU users |
| `results/builds.csv`, `results/generated_sources.csv` | build times and binary sizes; size of the generated Rust of the case studies |
| `results/machine.txt` | machine, toolchain, CLI binary and tree state of the recorded run |
| `results/summary.md` | tables generated from the CSV files (`run_bench.py summary`) |
| `results/excluded_batches.csv` | batches whose rows stay in the CSV files but are left out of every statistic, with the reason |
| `results/profiles.txt` | two sampling profiles of the LRL front half (context, not timing measurements) |
| `sample_summary.py` | condenses a macOS `sample` report into per-frame sample counts (used for `profiles.txt`) |
| `work/` | generated programs, Rust sources and binaries (ignored by git; `bench/.gitignore`); `work/bcheck/` holds those of the independent check's re-run |

## How to reproduce

From the repository root, on a quiet machine:

```sh
CARGO_TARGET_DIR=<dir> cargo build --release -p cli      # the recorded run used a fresh <dir>
ulimit -s 65520                                         # see "Stack" below
python3 bench/run_bench.py check                        # copied case-study forms still identical?
python3 bench/run_bench.py all --lrl <dir>/release/cli  # about 50 min of measuring here
```

(The batches used in the results ran 18:08:42-18:48:29 and, after an interruption described
under "Noise", 19:43:26-19:51:40, 48 minutes in total; timestamps in `results/batches.csv`.)

`all` runs, in order: `check`, `machine`, `compile`, `runtime`, `proof`, `rustref`, `indexcost`,
`summary`; each of them can also be run alone. New runs append to the CSV files; delete
`bench/results/*.csv` first for a clean set.

## Machine and toolchain of the recorded run

Recorded by `run_bench.py machine` into `results/machine.txt` (commands: `sysctl -n
machdep.cpu.brand_string`, `sysctl -n hw.ncpu`, `sysctl -n hw.perflevel0.physicalcpu`,
`sysctl -n hw.perflevel1.physicalcpu`, `sysctl -n hw.memsize`, `sw_vers`, `rustc -vV`, `cargo -V`):

- Apple M2 Pro, `hw.ncpu` 10 (6 performance + 4 efficiency cores), `hw.memsize` 34359738368 bytes
  (32 GiB); macOS 26.3 (build 25D125).
- rustc 1.78.0 (9b00956e5 2024-04-29), LLVM 18.1.2, host aarch64-apple-darwin; cargo 1.78.0;
  Python 3.11.9. `rustc` on `PATH` is the rustup proxy `~/.cargo/bin/rustc`, which both the LRL
  CLI and the driver invoke.
- The repository (and therefore the CLI's `build/` directory and `bench/work/`) is on an external
  drive: `diskutil info` reports File System Personality ExFAT, Protocol USB, Device Location
  External.
- Power: the measurements up to 18:52 ran on AC power; the re-measured batches of 19:43-19:51 ran
  on battery until 19:47:19 and on AC afterwards (`pmset -g log`); `pmset -g` at 19:43 reported
  `lowpowermode 0`.

## The LRL CLI that was measured

- A release build: `CARGO_TARGET_DIR=<scratch>/target_release cargo build --release -p cli`
  (default release profile; the workspace `Cargo.toml` has no `[profile]` section). Binary size
  5475088 bytes, sha256 `43640e57f8be283a369d266b2c2d2f0d325be3f69d53911d4de39c1a51f1da13`.
- Tree state: `git rev-parse HEAD` = `efe7bc09763b4755267f14a45556fa5b6dcb7a2f` plus uncommitted
  work (the JOT revision): `git status --short` listed 105 entries (84 modified, 19 untracked
  including `bench/` itself, 2 deleted), `git diff --shortstat` "86 files changed, 7946
  insertions(+), 2104 deletions(-)". Before the run, `find cli frontend kernel mir codegen stdlib
  Cargo.toml Cargo.lock -newer <cli binary> -type f` printed nothing, i.e. the binary was built
  from the measured sources. The same check (and an unchanged sha256 of the binary) was repeated
  before the re-measured batches at 19:43.

## Methodology

**Timing.** Every measurement is the wall-clock time of one child process, taken with
`time.perf_counter()` immediately before and after `subprocess.run(...)` with stdout and stderr
captured into pipes. Process start-up is therefore included in every number (see `size_only` and
the Rust reference for its size).

**Warm-up and repetitions.** Each configuration starts with one warm-up run whose duration fixes
the plan: if it took less than 1 s, a second warm-up run follows; then 20 measured runs if the
first warm-up took less than 0.5 s, 10 if less than 10 s, 5 otherwise. Warm-up runs are recorded
in the CSV files (`warmup=1`) but excluded from all statistics. The first execution of a freshly
linked binary is slow on this machine: for the 57 run-time configurations whose median is below
0.02 s, the first warm-up run took 0.242-0.318 s and the second 0.003-0.024 s. (XprotectService,
macOS's malware scanner, was among the busiest processes at 48 batch starts; whether it causes the
first-run cost was not examined.) The warm-up runs absorb this cost.

**Statistics.** `summary.md` reports, per configuration, the median, minimum and maximum of the
measured runs and their number. Scaling is reported as the ratio of medians between consecutive
sizes (n doubles) and its base-2 logarithm (the apparent exponent).

**Checks before each batch.** A batch is one configuration (for example: workload, n, backend,
flags). Before each batch the driver runs `ps` and waits (up to 10 min) while a `cargo`, `rustc`,
`lean`, `lake`, `leanc`, `idris2`, `racket`, `raco`, `ghc`, `cli` or `lrl*` process is running; it
then records `uptime` and the (at most three) busiest processes using at least 10% CPU
(`ps -A -r`) in `results/batches.csv`. Every run row also records the 1/5/15-minute load averages
(`os.getloadavg()`, the numbers `uptime` prints).

**Correctness of every run.** Every run-time workload and the Rust reference return n, the proof
pair returns A*B; the last `Result: ...` line of every run (warm-up runs included) is parsed and
compared with the expected value. In the run-time and Rust-reference experiments a mismatch or a
non-zero exit status ends that configuration (the run is recorded as `error:...`); in the proof
experiment such a run would be recorded as `error:...` and left out of the statistics (none
occurred). A compile-time run counts only if the CLI exits with status 0, prints `Compilation
successful` and does not fall back to another backend; the rustc rebuilds count only with exit
status 0.

**Stack.** The generated programs use stack space that grows with n (the largest sizes overflow
even a 64 MiB stack, see the results). With the default stack limit of this machine
(`ulimit -s` = 8176 KiB) the dynamic binary of `list_fold` overflowed its stack at n = 8000
(exploratory single run), so all measured processes run with the soft limit raised to the hard
limit, `ulimit -s 65520` (64 MiB), set in the shell that starts the driver (the driver refuses to
run with less; Python's `resource.setrlimit` was rejected by this macOS for every value tried).
Even so, the largest sizes overflow; those runs are recorded with status `stack overflow` and
documented below, not hidden.

**Two builds of every generated program.**
- `cli`: the binary produced by `lrl compile <file> --backend typed|dynamic -o <bin>`. The CLI
  writes the generated Rust to `build/output_<tag>.rs` and runs
  `rustc build/output_<tag>.rs -o build/output_<tag>.bin -C incremental=build/incremental`
  (`run_rustc` in `cli/src/compiler.rs`), i.e. without `-O`.
- `O`: the same generated file (copied out of `build/` by the driver) rebuilt with
  `rustc -O <file>.rs -o <bin>` (no other flag).

**Compile time (experiment 1).** For `case_studies/lrl/vectors.lrl` and `protocol.lrl`, per
backend (`--backend typed`, `--backend dynamic`):
- `cli_total`: `lrl compile <file> --backend <b> -o <bin>`, cwd = repository root;
- `cli_front_noop_rustc`: the same command with a no-op `rustc` script first on `PATH` (it only
  creates the `-o` file; `work/compile/shim/rustc`). This times the LRL front half: parsing,
  macro expansion, elaboration, kernel checking, MIR passes, Rust generation and writing the
  file, plus the start-up of the shim (a `/bin/sh` script);
- `rustc_cli_flags`: `rustc <generated>.rs -o <bin> -C incremental=<fresh empty directory>` on the
  generated file of the last `cli_total` run — the CLI's own flags. (The CLI itself passes
  `-C incremental=build/incremental`, a directory shared by all compiles; each compile writes a
  source file with a new name `output_<pid>_<nanos>.rs`. Whether rustc reuses anything from that
  directory was not examined; the comparison of front + rustc with the total below bounds the
  effect for these files.)
- `rustc_O`: `rustc -O <generated>.rs -o <bin>`.
The split front/rustc is cross-checked by comparing front + rustc with the measured total.

**Run time (experiment 2).** Workloads (templates in `programs/`), each instantiated for several
n, built with both backends, and each binary measured in both builds (`cli`, `O`):
- `vec_build_sum`: build a `Vec Nat n` of ones, sum it with the case study's `vsum`.
- `vec_rev_sum`: build a `Vec Nat n`, reverse it with the case study's `vreverse` (through
  `vsnoc`, so the algorithm itself is quadratic), sum it.
- `list_fold`: build a prelude `List Nat` of n ones, fold it with `log_sum` (protocol.lrl).
- `proto_send`: open a `Chan n`, send the n elements of a `Vec Nat n` with the case study's
  `send_all` (dependent elimination of the vector, one `#[once]` closure per element), close it,
  sum the receipt's log with `total`. The send operation is generated by the case study's
  `defsend` macro but with a non-printing encoder `quiet` instead of the printing `log`, so that n
  lines of output are not timed.
- `size_only`: only computes n; the start-up plus size-computation baseline.
The case-study forms are copied verbatim (`;; @copied-from` line in each template);
`run_bench.py check` verifies that they are still identical to the case-study files. Elements are
all 1 so that every `add` in the sums is cheap in both backends: the stdlib `add`
(`stdlib/prelude_api.lrl`) recurses on its first argument, the typed backend compiles it from that
definition, while the dynamic backend replaces it by a native addition (`runtime_nat_add`,
`mir/src/codegen.rs`). n is computed at run time as `(nat_mul A B)` from small literals; each
workload is a function of n applied to `size` in `main` (see "Compile-time evaluation of indices").
For each (workload, backend, flags) the sizes grow until a size's median exceeds 10 s or a run
fails; larger sizes are then recorded as `skipped`, with the reason (`a smaller n took more than
10 s (median)` or `the run at n=... failed`). (The recorded run's driver wrote the first reason in
both cases; the three affected rows of `results/runtime.csv`, all `list_fold` sizes after a stack
overflow, were corrected afterwards, see "Independent check".)

**Proof arguments (experiment 3).** `proof_arg_with.lrl` and `proof_arg_without.lrl` differ only
in the three lines marked `;; differs` (and in their header comments): `step` takes an extra
argument `h : Eq Nat n n` (a proof; `Eq` is a Prop in the prelude) that its body ignores, and its
caller passes `(refl Nat ih)`. `step` is called A*B times
(10^6 and 4*10^6). For each backend and build, the two binaries are run alternately (ABBA order,
15 rounds each, after 2 warm-up runs each), so slow drifts of the machine affect both alike.

**Plain Rust reference (experiment 4, context only).** `programs/rust_reference/vec_rev_sum.rs`,
built with `rustc -O`, run for the n of `vec_rev_sum`: `inplace` reverses a `Vec<u64>` of n ones in
place; `snoc` follows the algorithm of `vreverse` (one new vector per `vsnoc`). Only the factor
LRL/Rust is stated; nothing else is concluded from it.

**Compile-time evaluation of indices (experiment 5).** Front half (no-op `rustc`) of
`lrl compile --backend typed` for `vec_build_sum_closed_index.lrl`, where `main` is
`(vsum (vbuild size))` so that the closed expression `size` occurs in the type index
`Vec Nat size`, versus `vec_build_sum.lrl`, where the index is the variable n of `workload`.

**Clean-up.** After copying the generated source of a CLI compile, the driver deletes exactly the
files that compile created in the gitignored `build/` directory (`build/output_<tag>.rs` and the
incremental-cache directory `build/incremental/output_<tag>-*`). rustc also left empty temporary
directories `build/rmeta*` behind: 106 are dated during the recorded run (18:08-18:49), as many as
the CLI's rustc invocations in that period (39 `cli_total` runs and 67 builds), next to 7226 older
ones; the driver's own rustc rebuilds leave theirs in `work/`. They are not removed. (An earlier
version of this README said 53 and 7279; the independent check recounted.)

**Excluded batches.** A batch is excluded from the statistics only by listing it, with a reason,
in `results/excluded_batches.csv`; its rows stay in the raw CSV files and `summary.md` lists it.
One batch is excluded (see "Noise").

## Results

The tables are in [`results/summary.md`](results/summary.md) (generated; every number there is a
statistic of rows in `results/*.csv`). The observations below quote medians of wall-clock
seconds from there unless stated otherwise; "exponent" is log2 of the ratio of medians when n
doubles.

### 1. Compile time of the case studies

| program | backend | `lrl compile` total | LRL front half | rustc, CLI flags | rustc `-O` |
|---|---|---:|---:|---:|---:|
| vectors.lrl | typed | 9.450 | 7.923 (84% of total) | 1.910 | 3.764 |
| vectors.lrl | dynamic | 9.494 | 7.941 (84%) | 1.382 | 3.592 |
| protocol.lrl | typed | 1.910 | 0.600 (31%) | 1.270 | 1.866 |
| protocol.lrl | dynamic | 1.861 | 0.589 (32%) | 1.124 | 1.584 |

- Front half + rustc (CLI flags) is within -8.0% to +4.1% of the measured total, so the split
  accounts for the total.
- For `vectors.lrl` the LRL front half, not rustc, dominates, and it is the same for both
  backends. In one sampling profile of the first 6 s of that front half (`results/profiles.txt`;
  context, not a measurement), of the 4849 compiler-thread samples under
  `cli::compiler::compile_with_mir`, 62% were inside
  `mir::lower::LoweringContext::infer_term_type` (type inference during MIR lowering, which calls
  `kernel::checker::infer`) and 76% under the kernel's weak-head normaliser
  `kernel::checker::whnf_in_ctx`.
- Generated Rust: `vectors.lrl` 9536 lines (typed) and 25563 lines (dynamic), `protocol.lrl` 7298
  and 20135 lines; it also contains the prelude's definitions (for example `fn xor` and
  `fn write_file` at the end of both typed files).

### 2. Run time

Per workload, the largest sizes measured and the scaling at the last doubling
(`cli` = binary from `lrl compile`; `O` = generated Rust rebuilt with `rustc -O`):

| workload | typed `cli` | typed `O` | dynamic `cli` | dynamic `O` |
|---|---|---|---|---|
| `vec_build_sum` | 0.141 s at n=64000, exponent 0.95 | 0.080 s at 128000, 0.95 | 11.55 s at 4000, 1.99 | 18.75 s at 8000, 2.27 |
| `proto_send` | 0.120 s at 32000, 1.01 | 0.068 s at 64000, 0.96 | 11.57 s at 4000, 1.99 | 16.22 s at 8000, 2.07 |
| `list_fold` | 0.248 s at 128000, 0.99 | 0.141 s at 256000, 0.96 | 0.045 s at 32000, 0.96 | 0.035 s at 64000, 0.88 |
| `vec_rev_sum` | 1.036 s at 1600, 1.99 | 0.318 s at 1600, 1.93 | 15.48 s at 400, 2.96 | 37.33 s at 800, 2.99 |

- **Typed backend: linear where the algorithm is linear.** For `vec_build_sum`, `proto_send` and
  `list_fold` the exponent at the last doubling is 0.95-1.01; for `vec_rev_sum`, whose
  `vreverse` copies the vector once per element through `vsnoc` (a quadratic algorithm), it is
  1.93-1.99. No extra factor of n appears (in the generated typed code the recursive field of a
  vector is shared: `vcons(u64, T0, Rc<lrl_Vec<T0>>)`). At small n the start-up cost (below)
  dominates, so the exponents of the first doublings are lower.
- **Dynamic backend: one extra factor of n on vectors.** `vec_build_sum` and `proto_send` are
  quadratic (exponents 1.97-2.27) and `vec_rev_sum` cubic (2.88-3.00), while `list_fold` is linear
  and as fast as the typed backend (dynamic/typed 0.7-1.0). This matches how the dynamic backend
  represents values (`mir/src/codegen.rs`): `enum Value` is `#[derive(Clone)]`, a vector is a
  `Value::Inductive(String, usize, Vec<Value>)` whose clone copies the whole structure, every
  operand is passed as `.clone()` (`codegen_operand`), whereas a prelude list is
  `Value::List(Rc<List>)`, whose clone only increments a reference count. The measurements show
  the scaling; that this mechanism causes it is an inference from the code, not a measurement.
- **Backend ratio.** dynamic/typed grows with n: at n = 4000, 819x (`cli`) and 572x (`O`) for
  `vec_build_sum`, 639x and 552x for `proto_send`; 222x and 199x for `vec_rev_sum` at n = 400.
- **`rustc -O` vs the CLI's flags.** At the largest n measured in both builds the CLI binary is
  3.3-3.4 times slower than the `-O` rebuild with the typed backend (all four workloads) and
  2.4-3.3 times slower with the dynamic backend. `lrl compile` itself never passes `-O`.
- **Start-up and size computation.** `size_only` (computes n, nothing else) takes 2.5-3.8 ms for
  n <= 1600 in all four builds; this is the floor of every number here. Computing n itself grows
  with n in the typed backend (0.050 s `cli`, 0.012 s `O` at n = 256000) but not in the dynamic one
  (at most 0.0041 s): `nat_mul a b` (`stdlib/std/core/nat.lrl`) is `a` additions of `b`, and `add`
  recurses on its first argument in the typed backend but is native in the dynamic one.
- **Stack.** With a 64 MiB stack, these runs overflowed (status `stack overflow` in
  `results/runtime.csv`): typed `cli` at `vec_build_sum` n = 128000, `proto_send` 64000 and
  `list_fold` 256000; dynamic `cli` at `list_fold` 64000; dynamic `O` at `list_fold` 128000. The
  typed `O` builds ran at all three sizes where the typed `cli` builds overflowed. (The generated
  typed recursor computes the induction hypothesis by a recursive call, e.g.
  `rec_lrl_Vec_entry_0_impl` in `work/runtime/vec_build_sum_n1000_typed.rs`.)

### 3. Residual cost of a proof argument

Ratio with/without of medians (and of minima); extra time per call = difference of medians /
number of calls:

| calls | typed `cli` | typed `O` | dynamic `cli` | dynamic `O` |
|---:|---|---|---|---|
| 10^6 | 1.325 (1.322), 89 ns | 2.990 (3.063), 72 ns | 1.560 (1.559), 204 ns | 1.567 (1.587), 73 ns |
| 4*10^6 | 1.319 (1.329), 87 ns | 3.158 (3.181), 72 ns | 1.553 (1.569), 200 ns | 1.666 (1.625), 82 ns |

The proof argument is not free at run time in either backend. The generated code (kept in
`work/proof/` by the driver) shows why: the proof term itself is erased — no `refl` is built at the
call site, the argument is `()` (typed) or `Value::Unit` (dynamic) — but the proof's binder is
kept, so every call of `step` is two applications. Typed: `fn step() -> Rc<dyn LrlCallable<u64,
Rc<dyn LrlCallable<(), u64>>>>` (without the proof: `Rc<dyn LrlCallable<u64, u64>>`); the call
site applies `step` to `n` and the resulting closure to `()`. Dynamic: `f(_2.clone())` followed by
`f(Value::Unit)`. The ratios are large because `step`'s body is a single successor; they describe
this program, not the cost of proofs in general.

### 5. Compile time with a closed size expression in a type index

Front half (no-op `rustc`), typed backend:

| n | `main` = `(vsum (vbuild size))` (index closed) | `main` = `(workload size)` (index is a variable) |
|---:|---:|---:|
| 250 | 2.957 | 0.564 |
| 500 | 10.330 | 0.602 |
| 1000 | 38.941 | 0.622 |
| 2000 | 80.789 | 0.640 |

When the closed expression `size` (= `(nat_mul A B)`) occurs in a type index, the front half
grows steeply with n (ratios 3.49 and 3.77 for the first two doublings, 2.07 for the last; the
last size is written `(nat_mul 1000 2)`, the others `(nat_mul n 1)`), while with a variable index
it stays near 0.6 s. Two sampling profiles place this time in the kernel's evaluator
(`kernel::nbe`): profile (b) of `results/profiles.txt` (n = 1000, 15-25 s into the run) reaches it
from the kernel's definition check (`kernel::checker::Env::add_definition`); an exploratory
profile at n = 8000 (described there, raw report not kept in the repository) reaches it from MIR
lowering's `infer_term_type`. In an exploratory single run with n = 8000 the compile had not
finished after more than 10 minutes and was stopped. This is why every run-time workload passes n to a function instead of
writing `(vbuild size)` in `main`.

### Context only (experiment 4): a plain-Rust reference point

This subsection is not an LRL result and is kept apart from the others.
`programs/rust_reference/vec_rev_sum.rs` (`rustc -O`) takes 3.0-3.9 ms at every n from 100 to
1600 in both variants, i.e. it stays at the process start-up floor over this range. The factor LRL `O` / Rust (`inplace`) is 1.0 (n = 100) to 97 (n = 1600) for
the typed backend and 21 (n = 100) to 11533 (n = 800) for the dynamic backend; against the `snoc`
variant (same algorithm as `vreverse`) 1.3-82 and 25-11001. Since the Rust times do not grow with
n here, these factors grow only because the LRL times do. Nothing beyond the factors is concluded.

## Noise and threats to validity

- **Not an idle machine.** A process named `python` (three successive PIDs during the run; the
  last one, and an earlier one before the run, were identified with `ps` at 19:40 and 17:25 as a
  machine-learning script of an unrelated project) used 11-114% CPU (median 89%, i.e. about one
  of the 10 cores) at all 144 batch starts. No `cargo`, `rustc`, `lean` or other LRL process was
  running at any batch start. The 1-minute load average
  was 1.73-4.16 at batch starts (median 2.79) and at most 7.04 after any run. The measured
  programs are single-threaded, so one busy core should matter little, but it was not controlled.
- **No control of CPU frequency or core type.** macOS chooses between performance and efficiency
  cores and their clock; nothing was pinned.
- **Spread.** Over all 159 configurations, max/min - 1 has median 11.0% and maximum 111.3% (a
  2.8 ms `size_only` run: millisecond runs are dominated by start-up jitter). For the 67
  configurations with a median of at least 0.1 s it has median 4.1% and maximum 28.1%; 58 of them
  are within 10%. The nine above 10% are five compile-time configurations (rustc of
  `protocol.lrl` and `vectors.lrl`, and `protocol.lrl` dynamic `cli_total`), two of the slowest
  dynamic runs (`vec_build_sum` n = 4000 `cli`, `proto_send` n = 8000 `O`) and two proof-argument
  configurations. Differences of a few percent between configurations are not meaningful.
- **One interrupted batch.** The machine went to sleep at 18:53:12 (`pmset -g log`: "Clamshell
  Sleep", on battery from 18:52:46) during the closed-index n = 2000 batch of experiment 5; the run
  in progress measured 129.7 s against 77.6 and 79.3 s for the two runs before it, and the driver
  invocation wrote nothing after it. That batch is excluded (`results/excluded_batches.csv`); the
  closed-index and variable-index batches for n = 2000 were re-run at 19:43-19:51
  (`run_bench.py indexcost --indexcost-n 2000`) after the same pre-run checks, on battery power
  until 19:47:19 and on AC power afterwards. The two undisturbed runs of the excluded batch are 3.9%
  and 1.8% below the re-run's median.
- **Disk.** The repository, the CLI's `build/` directory and `bench/work/` are on an external USB
  drive (exFAT). Compile times include writing the generated Rust and the binaries there, and the
  CLI's rustc writes its incremental session into `build/incremental`, which already held several
  thousand session directories from earlier work.
- **First runs.** The first run of a freshly linked millisecond-scale binary took 0.24-0.32 s
  on this machine, the second 0.003-0.024 s (see "Warm-up and repetitions"); every number
  excludes warm-up runs.

## What these measurements do not show

- Nothing about other programs, other sizes, other machines or other rustc versions.
- No comparison with other languages except the context-only Rust factor of experiment 4, which
  compares a dependently typed functional program with an array program and is not evidence
  about LRL's design.
- Nothing about in-place update: for LRL the comparison (`case_studies/comparison/SUMMARY.md`,
  row Q11) records "no in-place update: the generated code allocates new cells".
- The proof experiment measures one shape of proof argument (an unused `Eq` argument of a
  first-order function whose body is one successor); other uses of proofs may cost more or less.
- The run-time workloads are small programs derived from two case studies; they are not
  representative of LRL programs in general, and sizes were limited by the 64 MiB stack and by
  stopping a configuration once a size's median exceeded 10 s.
- The sampling profiles locate where time went in single runs; they are not measurements and do
  not apportion the closed-index compile time between the kernel check and MIR lowering.

## Independent check

After the recorded run, a separate session checked the scripts, the texts and a sample of the
measurements (same machine, same release CLI binary, same sha256; no compiler source edited).

- **Scripts.** `run_bench.py` was read for methodological errors. Run-time numbers time only the
  built binary (the builds happen before, in the driver's `build_variants`); the CLI never
  runs the binary it builds (`build_native_binary` in `cli/src/compiler.rs` only moves it), so
  `cli_total` contains no first-run cost; every phase has warm-up runs; outputs are checked as
  described under "Correctness of every run". No error was found in what is timed. Two labels
  were wrong and are fixed: (1) a configuration stopped by a failed run recorded its larger sizes
  as `skipped: a smaller n took more than 10 s (median)`; the driver now records `skipped: the run
  at n=... failed`, and the three affected rows of `results/runtime.csv` (`list_fold` n = 128000
  and 256000 dynamic `cli`, n = 256000 dynamic `O`) were corrected in place (status text only);
  (2) the sentence of `summary.md` listing busy processes now says that at most three processes
  are recorded per batch. `summary.md` was regenerated; no number in it changed.
- **Numbers.** Before these fixes, `run_bench.py summary` run on copies of the CSV files
  reproduced `summary.md` byte for byte. Every number in this README that derives from the CSV
  files but is not in `summary.md` (first-run times, batch counts, load averages, CPU share of
  `python`, the nine configurations with a spread above 10%, the time span of the run) was
  recomputed from the CSV files with an independent script and matched; the numbers quoted from
  `summary.md` were compared with it; the machine and tree facts match `results/machine.txt` and
  `pmset -g log`; the profile counts of (a) were re-derived from the raw report; the `rmeta*`
  counts under "Clean-up" were wrong and are corrected there.
- **Re-run of a sample**, 20:12-20:42 the same day, with the same driver (only the labels above
  changed) and `--results-dir` outside the repository, `--work-dir bench/work/bcheck`: `machine`,
  `compile` (all), `runtime --workloads size_only,list_fold,vec_rev_sum,proto_send`, `proof`
  (all), `rustref` (all), `indexcost --indexcost-n 250,500`. The machine was busier than during
  the recorded run (1-minute load at batch starts 2.84-5.77, median 3.44; interactive browser
  processes among the busiest). Of the 133 configurations measured in both sessions, the
  relative difference of the medians (re-run / recorded - 1) has absolute median 5.2% and maximum
  37.0% (`vec_rev_sum` n = 100 typed `O`, 4.0 -> 5.5 ms); for the 55 configurations whose
  recorded median is at least 0.1 s it has absolute median 2.4% and maximum 22.9%, and 52 of them
  are within 10%. The three beyond 10%:
  `proto_send` dynamic `O` at n = 8000 (16.22 -> 19.93 s, +22.9%) and n = 4000 (+17.6%), and
  `rustc -O` of the typed `vectors.lrl` (3.764 -> 4.281 s, +13.7%). For the re-run workloads the
  stack overflows occurred at the same sizes and the scaling statements above hold: typed
  exponents at the last
  doubling 0.95-1.01 (`list_fold`, `proto_send`) and 1.99-2.01 (`vec_rev_sum`); dynamic 2.06-2.14
  (`proto_send`) and 2.98-3.03 (`vec_rev_sum`); proof ratios of medians 1.322 (typed `cli`),
  2.981-3.242 (typed `O`), 1.556-1.590 (dynamic `cli`), 1.551-1.640 (dynamic `O`), 72-214 ns extra
  per call. Between these two sessions, single medians of runs of 0.1 s or more differed by up
  to 22.9%, those of shorter runs by up to 37.0%.

## Audit note

Written by Claude (Anthropic) for the JOT revision, following the repository's no-fabrication rule
(`CLAUDE.md`). Every number in this README and in `results/summary.md` comes from a command run in
this session; the full chronological log, with each command and its output, is the session's
measurement log `B_measure.md` (kept outside the repository). What was verified, and how:

- Machine and toolchain: `sysctl -n machdep.cpu.brand_string` (Apple M2 Pro), `sysctl -n hw.ncpu`
  (10), `sysctl -n hw.perflevel0.physicalcpu` (6), `sysctl -n hw.perflevel1.physicalcpu` (4),
  `sysctl -n hw.memsize` (34359738368), `sw_vers` (26.3, 25D125), `rustc -vV` (1.78.0, LLVM 18.1.2),
  `cargo -V` (1.78.0), recorded by `run_bench.py machine` in `results/machine.txt`;
  `diskutil info "/Volumes/Crucial X6"` (ExFAT, USB, External); `pmset -g log`, `pmset -g batt`,
  `pmset -g` (sleep at 18:53:12, AC/battery times, `lowpowermode 0`).
- CLI build and tree state: `CARGO_TARGET_DIR=<scratch>/target_release cargo build --release -p
  cli` ("Finished `release` profile [optimized]"); `shasum -a 256` of the binary (twice, 18:08 and
  19:43, same value); `find cli frontend kernel mir codegen stdlib Cargo.toml Cargo.lock -newer
  <binary> -type f` (empty, twice); `git rev-parse HEAD`, `git status --short`,
  `git diff --shortstat` (in `results/machine.txt`); `git status --short history.txt` (clean
  before and after).
- Every timing: `python3 bench/run_bench.py all` (18:08) and `python3 bench/run_bench.py indexcost
  --indexcost-n 2000` (19:43), both from the repository root after `ulimit -s 65520`, with
  `LRL_BIN` set to the release binary; tables: `python3 bench/run_bench.py summary`. Copied
  case-study forms: `python3 bench/run_bench.py check` (0 problems). Derived ratios quoted above
  are in `results/summary.md` (tables "Split", "Ratios of medians", proof table) or are quotients
  of medians printed there.
- Exploratory single runs quoted (not part of the CSV data): the stack overflow of the dynamic
  `list_fold` binary at n = 8000 with the default 8176 KiB stack, the unfinished closed-index
  compile at n = 8000, and the `resource.setrlimit` failures, all before the timing run
  (`/usr/bin/time -p` or direct runs; logged in `B_measure.md`).
- Code facts, by `grep -n`/`sed -n` in this session: `run_rustc` and its `rustc` arguments
  (`.arg(source)`, `.arg("-o")`, `.arg(output)`, `.arg("-C")`, `incremental=`) in
  `cli/src/compiler.rs`, `PathBuf::from("build")` and the staged `output_<tag>.bin` there;
  `#[derive(Clone)] enum Value` with `List(Rc<List>)` and `Inductive(String, usize, Vec<Value>)`,
  `fn runtime_nat_add`, the `"add" =>` mapping and `fn codegen_operand` (`format!("{}.clone()", s)`)
  in `mir/src/codegen.rs`; no `"add"` in `mir/src/typed_codegen.rs`; `(def add` (matching on its
  first argument) and `(inductive Eq ... (sort 0))` in `stdlib/prelude_api.lrl`; `(def nat_mul` in
  `stdlib/std/core/nat.lrl`; `defsend`, `send_all`, `log`, `#[once]` in
  `case_studies/lrl/protocol.lrl`; `vsnoc`, `vreverse`, `vsum` in `case_studies/lrl/vectors.lrl`.
- Generated code facts, by `grep -n`/`sed -n` on the files the driver kept in `bench/work/`:
  `fn step()` signatures and the call sites in `work/proof/proof_arg_{with,without}_c1000000_typed.rs`
  and `..._dynamic.rs`, `grep -c refl` (0 in both typed files; only `fn refl()` in the dynamic one);
  `vcons(u64, T0, Rc<lrl_Vec<T0>>)`, `lrl_unshare` and `rec_lrl_Vec_entry_0_impl` in
  `work/runtime/vec_build_sum_n1000_typed.rs`; `fn xor()`/`fn write_file()` in
  `work/compile/{vectors,protocol}_typed.rs`.
- Profiles: `/usr/bin/sample` as described in `results/profiles.txt`, condensed with
  `bench/sample_summary.py`.
- Counts in "Noise": `results/batches.csv` (parsed with Python), `ls build/incremental | wc -l`
  (7386 entries), `find build -maxdepth 1 -name 'rmeta*' -newermt "2026-10-05 18:08" !
  -newermt "2026-10-05 20:00" | wc -l` (106) and `... ! -newermt "2026-10-05 18:08"` (7226), the
  last two run by the independent check.
- Not verified, and therefore not claimed: the cause of the first-run cost, the cause of the
  dynamic backend's extra factor of n (stated as an inference from the code), what part of the
  closed-index compile time is spent in the kernel check versus MIR lowering, and any statement
  about other machines, programs or compiler versions.

Independent check (section "Independent check"; a separate session whose log, `B_check.md`, is
kept outside the repository, like `B_measure.md`):

- `python3 bench/run_bench.py summary --results-dir <copy of results/>` and `diff` with
  `results/summary.md` (identical, before the fixes); `python3 bench/run_bench.py check`
  (0 problems); an independent Python script over `results/*.csv` for the README-only numbers
  (all matched); `shasum -a 256` of the release CLI (unchanged) and `find cli frontend kernel mir
  codegen stdlib Cargo.toml Cargo.lock -newer <binary> -type f` (empty) before the re-run.
- Re-run: from the repository root after `ulimit -s 65520`, under `caffeinate -i`, with `LRL_BIN`
  set to the same binary: `run_bench.py machine`, `compile`, `runtime --workloads
  size_only,list_fold,vec_rev_sum,proto_send`, `proof`, `rustref`, `indexcost --indexcost-n
  250,500`, `summary`, each with `--results-dir <scratch>` and `--work-dir bench/work/bcheck`
  (exit status 0). The comparison with `results/*.csv` (medians and minima per configuration,
  warm-up runs and excluded batches left out, as in `summary.md`) was computed by a separate
  script; the re-run's CSV files are kept with the session log, not in `results/`.
- Code facts re-checked by `grep -n`/`sed -n`: `run_rustc` and `build_native_binary` (the binary is
  moved with `fs::rename`, copy as fallback, and not executed) in `cli/src/compiler.rs`;
  `(def nat_mul` with `(add b ih)` in `stdlib/std/core/nat.lrl`; the generated-code facts listed
  above in `bench/work/`. Profile counts of (a) re-derived with `bench/sample_summary.py` from the
  raw report (4890 samples in the compiler thread, 4849 under `compile_with_mir`, 3003 under
  `infer_term_type`, 3662 under `whnf_in_ctx`).
