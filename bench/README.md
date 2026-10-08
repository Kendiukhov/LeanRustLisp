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
| `results/{compile_time,runtime,proof_arg,rust_reference,indexcost}.csv` | raw data: one row per run, including warm-up runs (flagged `warmup=1`), plus one row per configuration that was skipped (status `skipped: ...`) |
| `results/batches.csv` | one row per measurement batch: `uptime`, busy processes, top CPU users |
| `results/builds.csv`, `results/generated_sources.csv` | build times and binary sizes; size of the generated Rust of the case studies |
| `results/machine.txt` | machine, toolchain, CLI binary and tree state of the recorded run |
| `results/summary.md` | tables generated from the CSV files (`run_bench.py summary`) |
| `results/excluded_batches.csv` | only when needed: batches whose rows stay in the CSV files but are left out of every statistic, with the reason (the recorded run excludes no batch, so the file is absent) |
| `results/profiles.txt` | two sampling profiles of the LRL front half (context, not timing measurements) |
| `sample_summary.py` | condenses a macOS `sample` report into per-frame sample counts (used for `profiles.txt`) |
| `work/` | generated programs, Rust sources and binaries (ignored by git; `bench/.gitignore`) |

## How to reproduce

From the repository root, on a quiet machine (the recorded run did not have one; see "Noise"):

```sh
CARGO_TARGET_DIR=<dir> cargo build --release -p cli      # the recorded run used a fresh <dir>
ulimit -s 65520                                         # see "Stack" below
python3 bench/run_bench.py check                        # copied case-study forms still identical?
python3 bench/run_bench.py all --lrl <dir>/release/cli  # 39 min of measuring in the recorded run
```

(The recorded run is one invocation of `all` on 2026-10-08: its first batch started at 00:54:20
and its last run ended at 01:33:36, 39 minutes in total; timestamps in `results/batches.csv` and
in the `time` column of the other CSV files.)

`all` runs, in order: `check`, `machine`, `compile`, `runtime`, `proof`, `rustref`, `indexcost`,
`summary`; each of them can also be run alone. New runs append to the CSV files; delete
`bench/results/*.csv` first for a clean set (the recorded run started with an empty
`bench/results/`).

## Machine and toolchain of the recorded run

Recorded by `run_bench.py machine` into `results/machine.txt` (commands: `sysctl -n
machdep.cpu.brand_string`, `sysctl -n hw.ncpu`, `sysctl -n hw.perflevel0.physicalcpu`,
`sysctl -n hw.perflevel1.physicalcpu`, `sysctl -n hw.memsize`, `sw_vers`, `rustc -vV`, `cargo -V`):

- Apple M2 Pro, `hw.ncpu` 10 (6 performance + 4 efficiency cores), `hw.memsize` 34359738368 bytes
  (32 GiB); macOS 26.3 (build 25D125).
- rustc 1.78.0 (9b00956e5 2024-04-29), LLVM 18.1.2, host aarch64-apple-darwin; cargo 1.78.0
  (54d8815d0 2024-03-26); Python 3.11.9. `rustc` on `PATH` is the rustup proxy
  `~/.cargo/bin/rustc`, which both the LRL CLI and the driver invoke.
- The repository (and therefore the CLI's `build/` directory and `bench/work/`) is on an external
  drive: `diskutil info` reports File System Personality ExFAT, Protocol USB, Device Location
  External.
- Power: AC power throughout. `pmset -g batt` reported AC power before and after the run;
  `pmset -g log` has no sleep or wake entry and no change of power source on the day of the run.

## The LRL CLI that was measured

- A release build: `CARGO_TARGET_DIR=<scratch>/target_release_final cargo build --release -p cli`
  (default release profile; the workspace `Cargo.toml` has no `[profile]` section). Binary size
  5494336 bytes, sha256 `e50af7a629ec5801f3d0ffb4fa18b589476f6ccfcecd226861119e2fad349820`.
- Tree state: `git rev-parse HEAD` = `4eb6b1d3025b60f3f0b60c5479490cac068da99c`. `results/machine.txt`
  records `git status --short` outside results files and `paper/` as 2 entries (0 modified,
  2 untracked, 0 deleted) and `git diff --shortstat` as "19 files changed, 19 insertions(+), 3624
  deletions(-)". The tracked files that differed from `HEAD` were results files only: the earlier
  contents of `bench/results/`, moved out of the directory before the run so that it started empty
  (hence counted as deleted), and case-study results files (`results_*.md`) regenerated from that
  commit; the two untracked entries lie outside the compiler's sources. Before and after the run,
  `find cli frontend kernel mir codegen stdlib Cargo.toml Cargo.lock -newer <cli binary> -type f`
  printed nothing and the sha256 of the binary was unchanged, i.e. the binary was built from the
  measured sources.

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
0.02 s, the first warm-up run took 0.250-0.505 s and the second 0.003-0.026 s. (Processes of
macOS's XProtect malware protection, `XProtectRemediatorPirrit`, `XProtectRemediatorAdload`,
`XProtectRemediatorSnowBeagle` and `XprotectService`, were among the busiest processes at 109 of
the 142 batch starts; whether they cause the first-run cost was not examined.) The warm-up runs
absorb this cost.

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
even this stack, see the results). All measured processes therefore run with the soft stack
limit raised to the hard limit, `ulimit -s 65520` (65520 KiB, just under 64 MiB; recorded in `results/machine.txt`), set
in the shell that starts the driver; the default soft limit of this machine is lower. The driver
refuses to measure with a soft limit below 63 MiB (`check_stack`); Python's `resource.setrlimit`
was rejected by this macOS for every value tried. Even so, the largest sizes overflow; those runs
are recorded with status `stack overflow` and documented below, not hidden.

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
  directory, or is slowed down by it, was not examined; see the comparison of front + rustc with
  the measured total under "Results".)
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
The case-study forms are copied verbatim (`;; @copied-from` line in each template that copies case-study forms);
`run_bench.py check` verifies that they are still identical to the case-study files. Elements are
all 1 so that every `add` in the sums is cheap in both backends: the stdlib `add`
(`stdlib/prelude_api.lrl`) recurses on its first argument, the typed backend compiles it from that
definition, while the dynamic backend replaces it by a native addition (`runtime_nat_add`,
`mir/src/codegen.rs`). n is computed at run time as `(nat_mul A B)` from small literals; each
workload is a function of n applied to `size` in `main` (see "Compile-time evaluation of indices").
For each (workload, backend, flags) the sizes grow until a size's median exceeds 10 s or a run
fails; larger sizes are then recorded as `skipped`, with the reason (`a smaller n took more than
10 s (median)` or `the run at n=... failed`).

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
`Vec Nat size`, versus `vec_build_sum.lrl`, where the index is the variable n of `workload`; for
n = 250, 500 and 1000, each written as `(nat_mul n 1)`.

**Clean-up.** After copying the generated source of a CLI compile, the driver deletes the files
that compile leaves in the gitignored `build/` directory (`build/output_<tag>.rs` and the
incremental-cache directory `build/incremental/output_<tag>-*`; the binary is moved out by the
CLI). rustc also leaves empty temporary directories `build/rmeta*` behind; they are not removed.
After the recorded run, the only entries of `build/` dated during the run were such empty
`rmeta*` directories and `build/incremental` itself, which kept no session directory of the run.
The driver's own rustc rebuilds leave their `rmeta*` directories in `work/`.

**Excluded batches.** A batch is excluded from the statistics only by listing it, with a reason,
in `results/excluded_batches.csv`; its rows stay in the raw CSV files and `summary.md` lists it.
No batch of the recorded run is excluded (see "Noise").

## Results

The tables are in [`results/summary.md`](results/summary.md) (generated by `run_bench.py summary`
from `results/*.csv` and `results/machine.txt`: medians, minima, maxima and ratios of the measured
rows, single rows such as build times and sizes, and the machine block). The observations below quote medians of wall-clock
seconds from there unless stated otherwise; "exponent" is log2 of the ratio of medians when n
doubles.

### 1. Compile time of the case studies

| program | backend | `lrl compile` total | LRL front half | rustc, CLI flags | rustc `-O` |
|---|---|---:|---:|---:|---:|
| vectors.lrl | typed | 12.472 | 9.988 (80% of total) | 1.658 | 3.725 |
| vectors.lrl | dynamic | 12.814 | 9.995 (78%) | 1.392 | 3.304 |
| protocol.lrl | typed | 2.845 | 0.8155 (29%) | 1.164 | 1.748 |
| protocol.lrl | dynamic | 3.669 | 0.8134 (22%) | 1.033 | 1.535 |

- Front half + rustc (CLI flags) is below the measured total by 6.6% (`vectors.lrl` typed),
  11.1% (`vectors.lrl` dynamic), 30.4% (`protocol.lrl` typed) and 49.7% (`protocol.lrl`
  dynamic), i.e. by 0.826-1.823 s: in this run the two separately timed parts do not account for
  the whole of `lrl compile`. Where the remaining time goes was not examined (the CLI's own rustc
  call uses the shared `build/incremental`, the separately timed one a fresh empty directory; see
  "Compile time" under "Methodology").
- For `vectors.lrl` the LRL front half, not rustc, dominates (80% and 78% of the total), and it
  is the same for both backends (9.988 and 9.995 s). In one sampling profile of the first 6 s of
  that front half (`results/profiles.txt`, profile (a); context, not a measurement), of the 4334
  compiler-thread samples under `cli::compiler::compile_with_mir`, 3246 were in MIR lowering
  (`mir::lower::LoweringContext::lower_term`, called from `cli::driver::validate_definition_mir`),
  72% were inside `mir::lower::LoweringContext::infer_term_type` (type inference during MIR
  lowering, which calls `kernel::checker::infer`) and 73% under the kernel's weak-head normaliser
  `kernel::checker::whnf_in_ctx`.
- Generated Rust: `vectors.lrl` 9536 lines (typed) and 25475 lines (dynamic), `protocol.lrl` 7298
  and 20135 lines; it also contains the prelude's definitions (for example `fn xor` and
  `fn write_file` at the end of both typed files).

### 2. Run time

Per workload, the largest sizes measured and the scaling at the last doubling
(`cli` = binary from `lrl compile`; `O` = generated Rust rebuilt with `rustc -O`):

| workload | typed `cli` | typed `O` | dynamic `cli` | dynamic `O` |
|---|---|---|---|---|
| `vec_build_sum` | 0.1377 s at n=64000, exponent 0.94 | 0.0795 s at 128000, 0.90 | 11.446 s at 4000, 2.01 | 17.999 s at 8000, 2.28 |
| `proto_send` | 0.1204 s at 32000, 0.93 | 0.0717 s at 64000, 0.91 | 11.259 s at 4000, 1.98 | 18.402 s at 8000, 2.28 |
| `list_fold` | 0.2489 s at 128000, 0.97 | 0.1419 s at 256000, 0.96 | 0.0465 s at 32000, 0.92 | 0.0354 s at 64000, 0.88 |
| `vec_rev_sum` | 1.017 s at 1600, 1.97 | 0.3163 s at 1600, 1.94 | 15.072 s at 400, 2.97 | 36.289 s at 800, 3.03 |

- **Typed backend: linear where the algorithm is linear.** For `vec_build_sum`, `proto_send` and
  `list_fold` the exponent at the last doubling is 0.90-0.97; for `vec_rev_sum`, whose
  `vreverse` copies the vector once per element through `vsnoc` (a quadratic algorithm), it is
  1.94-1.97. No extra factor of n appears (in the generated typed code the recursive field of a
  vector is shared: `vcons(u64, T0, Rc<lrl_Vec<T0>>)`). At small n the start-up cost (below)
  dominates, so the exponents of the first doublings are lower.
- **Dynamic backend: one extra factor of n on vectors.** `vec_build_sum` and `proto_send` are
  quadratic (exponents 1.98-2.28) and `vec_rev_sum` cubic (2.84-3.03), while `list_fold` is linear
  and roughly as fast as the typed backend (dynamic/typed 0.7-1.1). This matches how the dynamic
  backend represents values (`mir/src/codegen.rs`): `enum Value` is `#[derive(Clone)]`, a vector is
  a `Value::Inductive(String, usize, Vec<Value>)` whose clone copies the whole structure, every
  operand is passed as `.clone()` (`codegen_operand`), whereas a prelude list is
  `Value::List(Rc<List>)`, whose clone only increments a reference count. The measurements show
  the scaling; that this mechanism causes it is an inference from the code, not a measurement.
- **Backend ratio.** dynamic/typed grows with n: at n = 4000, 899.2 (`cli`) and 670.5 (`O`) for
  `vec_build_sum`, 602.2 and 496.0 for `proto_send`; 224.2 and 195.0 for `vec_rev_sum` at n = 400.
- **`rustc -O` vs the CLI's flags.** At the largest n measured in both builds the CLI binary is
  3.1-3.4 times slower than the `-O` rebuild with the typed backend (all four workloads) and
  2.4-3.4 times slower with the dynamic backend. `lrl compile` itself never passes `-O`.
- **Start-up and size computation.** `size_only` (computes n, nothing else) takes 2.9-4.3 ms
  (medians) for n <= 1600 in all four builds; this is the floor of every number here. Computing n
  itself grows with n in the typed backend (0.0498 s `cli`, 0.0114 s `O` at n = 256000) but not in
  the dynamic one (medians at most 0.0040 s): `nat_mul a b` (`stdlib/std/core/nat.lrl`) is `a`
  additions of `b`, and `add` recurses on its first argument in the typed backend but is native in
  the dynamic one.
- **Stack.** With the 65520 KiB stack, these runs overflowed (status `stack overflow` in
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
| 10^6 | 1.307 (1.305), 84 ns | 3.040 (3.013), 72 ns | 1.548 (1.541), 198 ns | 1.564 (1.564), 73 ns |
| 4*10^6 | 1.321 (1.331), 87 ns | 3.146 (3.153), 72 ns | 1.533 (1.538), 189 ns | 1.675 (1.659), 82 ns |

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
| 250 | 1.788 | 0.7502 |
| 500 | 4.854 | 0.7756 |
| 1000 | 16.898 | 0.8127 |

When the closed expression `size` (= `(nat_mul n 1)` at all three sizes) occurs in a type index,
the front half grows faster than linearly with n (ratios of medians 2.72 and 3.48 for the two
doublings) and at n = 1000 takes 20.8 times as long as with a variable index, which stays between
0.7502 and 0.8127 s. Profile (b) of `results/profiles.txt` (n = 1000, 5-15 s into the run; context,
not a measurement) places most of this time in the kernel's evaluator: 3501 of its 5388
compiler-thread samples have a frame of `kernel::nbe` as outermost recorded frame. Only 288
recorded stacks reach the driver; of these, 166 are under the kernel's definition check
(`kernel::checker::Env::add_definition`) and 122 under MIR lowering
(`mir::lower::LoweringContext::lower_term`), both reaching the evaluator, so the profile does not
apportion the time between the two. This is why every run-time workload passes n to a function
instead of writing `(vbuild size)` in `main`.

### Context only (experiment 4): a plain-Rust reference point

This subsection is not an LRL result and is kept apart from the others.
`programs/rust_reference/vec_rev_sum.rs` (`rustc -O`) takes 2.2-2.7 ms (medians) at every n from
100 to 1600 in both variants. The factor LRL `O` / Rust (`inplace`) is 1.7 (n = 100) to 141
(n = 1600) for the typed backend and 29 (n = 100) to 15923 (n = 800) for the dynamic backend;
against the `snoc` variant (same algorithm as `vreverse`) 2.0-126 and 34-15413. Since the Rust
medians stay within this narrow range, these factors grow because the LRL times do. Nothing beyond
the factors is concluded.

## Noise and threats to validity

- **Not an idle machine.** Background system processes were busy throughout. Among the (at most
  three) busiest processes recorded at the 142 batch starts were `StorageManagementService` (at 129
  batch starts, 27.0-113.9% CPU), `XProtectRemediatorPirrit` (105, 27.6-94.9%),
  `ApplicationsStorageExtension` (104, 35.5-79.3%), `Storage` (29) and `UVFSService` (12); the full
  list is in `results/summary.md`. No `cargo`, `rustc`, `lean` or other LRL process was running at
  any batch start. The 1-minute load average was 4.12-8.19 at batch starts (median 5.30) and at
  most 7.55 after any run; when the run started, the 5- and 15-minute load averages were still
  13.93 and 19.38 (`results/machine.txt`), i.e. the machine had been more heavily loaded shortly
  before. The measured programs are single-threaded, so busy cores should matter little, but this
  was not controlled.
- **No control of CPU frequency or core type.** macOS chooses between performance and efficiency
  cores and their clock; nothing was pinned.
- **Spread.** Over all 157 configurations, max/min - 1 has median 8.6% and maximum 239.6% (`size_only`
  n = 1000 dynamic `O`, median 0.0040 s: millisecond runs are dominated by start-up jitter). For the
  65 configurations with a median of at least 0.1 s it has median 2.5% and maximum 26.3%; 61 of
  them are within 10%. The four above 10% are `rustc -O` and rustc with the CLI's flags of the
  dynamic `protocol.lrl` (26.3% and 17.5%), the `with` binary of the dynamic `cli` proof pair at
  10^6 calls (21.8%), and the variable-index front half at n = 1000 of experiment 5 (11.7%).
  Differences of a few percent between configurations are not meaningful.
- **No excluded batch.** The run was not interrupted (no sleep in `pmset -g log`, AC power
  throughout, `all` exited with status 0), and no batch is excluded.
- **Disk.** The repository, the CLI's `build/` directory and `bench/work/` are on an external USB
  drive (exFAT). Compile times include writing the generated Rust and the binaries there, and the
  CLI's rustc writes its incremental session into `build/incremental`, which already held session
  directories of earlier compiles.
- **First runs.** The first run of a freshly linked millisecond-scale binary took 0.250-0.505 s
  on this machine, the second 0.003-0.026 s (see "Warm-up and repetitions"); every number
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
  representative of LRL programs in general, and sizes were limited by the 65520 KiB stack and by
  stopping a configuration once a size's median exceeded 10 s.
- The sampling profiles locate where time went in single runs; they are not measurements and do
  not apportion the closed-index compile time between the kernel check and MIR lowering.
- Nothing about where the part of `lrl compile` that front half + rustc do not account for is
  spent.

## Audit note

Written by Claude (Anthropic) for the JOT revision, following the repository's no-fabrication rule
(`CLAUDE.md`). This README describes the run recorded in `results/` (2026-10-08, CLI sha256
`e50af7a6...`, `HEAD` `4eb6b1d`). The measuring commands are listed below; every figure was then
checked against the files in `results/` as described here.

Where each kind of figure comes from:

- Machine, toolchain, Python version, CLI binary size and sha256, `HEAD`, the `git status` and
  `git diff --shortstat` counts, the stack limit and the load averages at the start of the run:
  `results/machine.txt` (written by `run_bench.py machine`).
- Medians, minima, maxima and run counts; ratios of medians and exponents; dynamic/typed and
  `cli`/`O` ratios; front-half shares; proof ratios and ns per call; Rust factors; generated-source
  line counts; batch count, load-average statistics, the list of busy processes and the spread
  statistics: `results/summary.md` (`python3 bench/run_bench.py summary`).
- Arithmetic on figures printed in `summary.md` (front + rustc versus the total, in % and s; the
  closed-index ratios 2.72 and 3.48 and the factor 20.8; ranges over several table cells):
  recomputed from the medians in the CSV files (the ratios) or from the figures in `summary.md`.
- Figures read from the CSV files but not printed in `summary.md`: the time span of the run
  (`results/batches.csv` and the `time` column of the other CSV files), the warm-up times of the 57
  fast run-time configurations (`results/runtime.csv`), the number of batch starts per process and
  its CPU range, and the 109 batch starts with an XProtect process (`results/batches.csv`), the four
  configurations with a spread above 10% (all run CSV files): computed directly from
  `results/*.csv`.
- Profile counts and percentages: `results/profiles.txt`.
- Methodology constants (repetitions, thresholds, sizes, numbers of calls and rounds, the 63 MiB
  stack check): `bench/run_bench.py` as committed.

Commands of the measurement session: `CARGO_TARGET_DIR=<scratch>/target_release_final
cargo build --release -p cli` ("Finished `release` profile [optimized]"); `shasum -a 256` of the
binary and `find cli frontend kernel mir codegen stdlib Cargo.toml Cargo.lock -newer <binary>
-type f` (empty) before and after the run; `python3 bench/run_bench.py all --lrl <binary>` from
the repository root after `ulimit -s 65520`, alongside `caffeinate -i` (exit status 0); afterwards
`python3 bench/run_bench.py check` (0 problems) and `python3 bench/run_bench.py summary`
(identical to the summary written by `all`); `pmset -g log` and `pmset -g batt` (no sleep, AC
power); the two profiles with `/usr/bin/sample` and `bench/sample_summary.py` as described in
`results/profiles.txt`.

Verified while writing this README:

- Code facts, by `grep -n`/`sed -n`: `run_rustc` and its arguments (`.arg(source)`, `.arg("-o")`,
  `.arg(output)`, `.arg("-C")`, `incremental=`; no `-O`), `PathBuf::from("build")`, the
  `<pid>_<nanos>` tag, the staged `output_<tag>.bin`/`output_<tag>.rs` and `move_compiled_binary`
  (rename, else copy and remove) in `cli/src/compiler.rs`;
  `#[derive(Clone)] enum Value` with `List(Rc<List>)` and `Inductive(String, usize, Vec<Value>)`,
  `fn runtime_nat_add`, the `"add" =>` mapping and `fn codegen_operand` (`format!("{}.clone()", s)`)
  in `mir/src/codegen.rs`; no `"add"` in `mir/src/typed_codegen.rs`; `(def add` (matching on its
  first argument) and `(inductive Eq ... (sort 0))` in `stdlib/prelude_api.lrl`; `(def nat_mul`
  with `(add b ih)` in `stdlib/std/core/nat.lrl`; `defsend`, `send_all`, `log`, `#[once]`,
  `log_sum`, `total` in `case_studies/lrl/protocol.lrl`; `vsnoc`, `vreverse`, `vsum` in
  `case_studies/lrl/vectors.lrl`; the `;; @copied-from` and `;; differs` lines, `(refl Nat ih)` and
  `quiet` in `bench/programs/`; no `[profile` in `Cargo.toml`; the profile frames named above
  (`fn infer_term_type`, `fn lower_term` in `mir/src/lower.rs`, `fn whnf_in_ctx`, `fn infer`,
  `fn add_definition` in `kernel/src/checker.rs`, `fn compile_with_mir` in `cli/src/compiler.rs`,
  `fn validate_definition_mir` in `cli/src/driver.rs`); the row Q11 text in
  `case_studies/comparison/SUMMARY.md`.
- Generated code facts, by `grep -n`/`sed -n` on the files of the recorded run in `bench/work/`:
  `fn step()` signatures and the call sites in `work/proof/proof_arg_{with,without}_c1000000_typed.rs`
  and `..._dynamic.rs`, `grep -c refl` (0 in both typed files; only `fn refl()` in the dynamic one);
  `vcons(u64, T0, Rc<lrl_Vec<T0>>)` and `rec_lrl_Vec_entry_0_impl` (with its recursive call) in
  `work/runtime/vec_build_sum_n1000_typed.rs`; `fn xor()`/`fn write_file()` near the end of
  `work/compile/{vectors,protocol}_typed.rs`.
- Environment: `command -v rustc` in a login shell (`~/.cargo/bin/rustc`, the same file as
  `~/.cargo/bin/rustup`); `ulimit -s` and `ulimit -Hs` (the soft default is lower than the hard
  limit 65520); `resource.setrlimit(RLIMIT_STACK, ...)` raising `ValueError` for every value tried;
  `diskutil info "/Volumes/Crucial X6"` (ExFAT, USB, External); `pmset -g batt` (AC power) and
  `pmset -g log` (no sleep, wake or power-source entry on 2026-10-08); `find build -maxdepth 1
  -newermt <start of run> ! -newermt <end of run>` (only empty `rmeta*` directories and
  `build/incremental`), the same for `build/incremental` (no session directory of the run) and
  for `bench/work` (`rmeta*` directories).
- Not verified, and therefore not claimed: the cause of the first-run cost, the cause of the part
  of `lrl compile` that front half + rustc do not account for, the cause of the dynamic backend's
  extra factor of n (stated as an inference from the code), what part of the closed-index compile
  time is spent in the kernel check versus MIR lowering, and any statement about other machines,
  programs or compiler versions.
