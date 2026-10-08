# Provenance of the figures in numbers.tex

Generated from the repository root by

    python3 paper/jot_r1/scripts/collect_numbers.py --test-log <log of `cargo test --all --no-fail-fast`>

The test counts come from paper/jot_r1/test_summary.txt, which the script extracts from that log (its first line records the tested revision).

| macro | value | command or source |
|---|---|---|
| `\NumRustLines` | 89\,364 | `find kernel frontend mir cli codegen -name '*.rs' -not -name '._*' -type f -print0 | xargs -0 cat | wc -l` |
| `\NumRustFiles` | 106 | `find kernel frontend mir cli codegen -name '*.rs' -not -name '._*' -type f | wc -l` |
| `\NumKernelSrcLines` | 14\,216 | `find kernel/src -name '*.rs' -not -name '._*' -type f -print0 | xargs -0 cat | wc -l` |
| `\NumKernelTestLines` | 8967 | `find kernel/tests -name '*.rs' -not -name '._*' -type f -print0 | xargs -0 cat | wc -l` |
| `\NumFrontendSrcLines` | 9525 | `find frontend/src -name '*.rs' -not -name '._*' -type f -print0 | xargs -0 cat | wc -l` |
| `\NumFrontendTestLines` | 3815 | `find frontend/tests -name '*.rs' -not -name '._*' -type f -print0 | xargs -0 cat | wc -l` |
| `\NumMirSrcLines` | 26\,457 | `find mir/src -name '*.rs' -not -name '._*' -type f -print0 | xargs -0 cat | wc -l` |
| `\NumMirTestLines` | 2708 | `find mir/tests -name '*.rs' -not -name '._*' -type f -print0 | xargs -0 cat | wc -l` |
| `\NumCliSrcLines` | 8498 | `find cli/src -name '*.rs' -not -name '._*' -type f -print0 | xargs -0 cat | wc -l` |
| `\NumCliTestLines` | 15\,175 | `find cli/tests -name '*.rs' -not -name '._*' -type f -print0 | xargs -0 cat | wc -l` |
| `\NumCodegenSrcLines` | 3 | `find codegen/src -name '*.rs' -not -name '._*' -type f -print0 | xargs -0 cat | wc -l` |
| `\NumCodegenTestLines` | 0 | `(no codegen/tests directory)` |
| `\NumKernelNonTestLines` | 10\,222 | `kernel/src/*.rs without test_support.rs and without #[cfg(test)] items (scripts/collect_numbers.py:strip_test_modules)` |
| `\NumTestFns` | 940 | `grep -rh --include='*.rs' -E '^\s*#\[test\]' kernel frontend mir cli codegen | wc -l` |
| `\NumTestsPassed` | 940 | `sum of 'test result' lines in paper/jot_r1/test_summary.txt (extracted from the cargo test log)` |
| `\NumTestsFailed` | 0 | `sum of 'test result' lines in paper/jot_r1/test_summary.txt` |
| `\NumTestsIgnored` | 0 | `sum of 'test result' lines in paper/jot_r1/test_summary.txt` |
| `\NumLrlFiles` | 404 | `find tests code_examples stdlib case_studies -name '*.lrl' -not -name '._*' -type f | wc -l` |
| `\NumVectorsLines` | 200 | `wc -l < case_studies/lrl/vectors.lrl` |
| `\NumProtocolLines` | 106 | `wc -l < case_studies/lrl/protocol.lrl` |
| `\NumVectorsTheorems` | 7 | `grep -c '^THEOREM ' case_studies/lrl/results_vectors.md` |
| `\NumCaseNegatives` | 15 | `find case_studies/lrl/neg -name '*.lrl' -not -name '._*' | wc -l` |
| `\NumCorpusClasses` | 31 | `manifest.tsv rows with kind != positive` |
| `\NumCorpusPositives` | 19 | `manifest.tsv rows with kind == positive` |
| `\NumCorpusFiles` | 100 | `find case_studies/corpus -name '*.lrl' -not -name '._*' | wc -l` |
| `\NumCorpusMatch` | 50 | `results_corpus.md headline` |
| `\NumCorpusRows` | 50 | `results_corpus.md headline` |
| `\NumCmpLeanIdrisCases` | 71 | `results_lean_idris.md headline` |
| `\NumCmpLeanIdrisMatch` | 71 | `results_lean_idris.md headline` |
| `\NumCmpRustRacketCases` | 114 | `results_rust_racket.md headline` |
| `\NumCmpRustRacketMatch` | 114 | `results_rust_racket.md headline` |
| `\NumCmpLrlCases` | 86 | `results_lrl.md headline` |
| `\NumCmpLrlMatch` | 86 | `results_lrl.md headline` |
| `\NumCmpFilesLean` | 27 | `find case_studies/comparison/lean -name '*.lean' -not -name '._*' | wc -l` |
| `\NumCmpFilesIdrisTwo` | 31 | `find case_studies/comparison/idris2 -name '*.idr' -not -name '._*' | wc -l` |
| `\NumCmpFilesRust` | 16 | `find case_studies/comparison/rust -name '*.rs' -not -name '._*' | wc -l` |
| `\NumCmpFilesRacket` | 68 | `find case_studies/comparison/racket -name '*.rkt' -not -name '._*' | wc -l` |
| `\NumCmpFilesLrl` | 41 | `find case_studies/comparison/lrl -name '*.lrl' -not -name '._*' | wc -l` |
| `\NumStageCorpusBoth` | 14 | `results_stage_matrix.md, section 1 summary: 'kernel and MIR both reject'` |
| `\NumStageCorpusKernelOnly` | 3 | `results_stage_matrix.md, section 1 summary: 'kernel rejects, MIR does not'` |
| `\NumStageCorpusMirOnly` | 6 | `results_stage_matrix.md, section 1 summary: 'MIR only (kernel accepts)'` |
| `\NumStageCorpusElab` | 4 | `results_stage_matrix.md, section 1 summary: 'elaborator or expander only (no core term)'` |
| `\NumStageCorpusDecl` | 2 | `results_stage_matrix.md, section 1 summary: 'declaration-level (inductive) check'` |
| `\NumStageCorpusBoundary` | 2 | `results_stage_matrix.md, section 1 summary: 'macro boundary at expansion'` |
| `\NumStageFiles` | 222 | `results_stage_matrix.md section 2 (dynamic prelude)` |
| `\NumStageDefs` | 489 | `results_stage_matrix.md section 2 (dynamic prelude)` |
| `\NumStageExprs` | 72 | `results_stage_matrix.md section 2 (dynamic prelude)` |
| `\NumStageElabPass` | 538 | `results_stage_matrix.md section 2, row 'elaboration'` |
| `\NumStageElabReject` | 23 | `results_stage_matrix.md section 2, row 'elaboration'` |
| `\NumStageKTypingPass` | 538 | `results_stage_matrix.md section 2, row 'kernel typing'` |
| `\NumStageKTypingReject` | 0 | `results_stage_matrix.md section 2, row 'kernel typing'` |
| `\NumStageKAdmitPass` | 534 | `results_stage_matrix.md section 2, row 'kernel admission (add_definition)'` |
| `\NumStageKAdmitReject` | 4 | `results_stage_matrix.md section 2, row 'kernel admission (add_definition)'` |
| `\NumStageKOwnPass` | 534 | `results_stage_matrix.md section 2, row 'kernel ownership walk'` |
| `\NumStageKOwnReject` | 4 | `results_stage_matrix.md section 2, row 'kernel ownership walk'` |
| `\NumStageMLowerPass` | 538 | `results_stage_matrix.md section 2, row 'MIR lowering'` |
| `\NumStageMLowerReject` | 0 | `results_stage_matrix.md section 2, row 'MIR lowering'` |
| `\NumStageMTypingPass` | 538 | `results_stage_matrix.md section 2, row 'MIR typing'` |
| `\NumStageMTypingReject` | 0 | `results_stage_matrix.md section 2, row 'MIR typing'` |
| `\NumStageMOwnPass` | 534 | `results_stage_matrix.md section 2, row 'MIR ownership'` |
| `\NumStageMOwnReject` | 4 | `results_stage_matrix.md section 2, row 'MIR ownership'` |
| `\NumStageMBorrowPass` | 536 | `results_stage_matrix.md section 2, row 'MIR borrow check (NLL)'` |
| `\NumStageMBorrowReject` | 2 | `results_stage_matrix.md section 2, row 'MIR borrow check (NLL)'` |
| `\NumStageCliPass` | 532 | `results_stage_matrix.md section 2, row 'CLI admits (replay)'` |
| `\NumStageCliReject` | 29 | `results_stage_matrix.md section 2, row 'CLI admits (replay)'` |
| `\NumStageKAcceptMReject` | 2 | `results_stage_matrix.md section 2` |
| `\NumStageKRejectMAccept` | 0 | `results_stage_matrix.md section 2` |
| `\NumStageCliAgree` | 329 | `results_stage_matrix.md cross-check` |
| `\NumStageCliFiles` | 329 | `results_stage_matrix.md cross-check` |
| `\BenchVectorsTypedTotal` | 12.472 | `bench/results/summary.md: vectors typed cli_total median` |
| `\BenchVectorsTypedFront` | 9.988 | `bench/results/summary.md: vectors typed front-half median` |
| `\BenchVectorsTypedRustcO` | 3.725 | `bench/results/summary.md: vectors typed rustc -O median` |
| `\BenchVectorsDynamicTotal` | 12.814 | `bench/results/summary.md: vectors dynamic cli_total median` |
| `\BenchVectorsDynamicFront` | 9.995 | `bench/results/summary.md: vectors dynamic front-half median` |
| `\BenchVectorsDynamicRustcO` | 3.304 | `bench/results/summary.md: vectors dynamic rustc -O median` |
| `\BenchProtocolTypedTotal` | 2.845 | `bench/results/summary.md: protocol typed cli_total median` |
| `\BenchProtocolTypedFront` | 0.8155 | `bench/results/summary.md: protocol typed front-half median` |
| `\BenchProtocolTypedRustcO` | 1.748 | `bench/results/summary.md: protocol typed rustc -O median` |
| `\BenchProtocolDynamicTotal` | 3.669 | `bench/results/summary.md: protocol dynamic cli_total median` |
| `\BenchProtocolDynamicFront` | 0.8134 | `bench/results/summary.md: protocol dynamic front-half median` |
| `\BenchProtocolDynamicRustcO` | 1.535 | `bench/results/summary.md: protocol dynamic rustc -O median` |
| `\BenchVecBuildSumN` | 4000 | `bench/results/summary.md: chosen size for vec_build_sum` |
| `\BenchVecBuildSumTypedCli` | 0.0127 | `bench/results/summary.md: vec_build_sum n=4000 typed cli median` |
| `\BenchVecBuildSumTypedO` | 0.0055 | `bench/results/summary.md: vec_build_sum n=4000 typed O median` |
| `\BenchVecBuildSumDynamicCli` | 11.446 | `bench/results/summary.md: vec_build_sum n=4000 dynamic cli median` |
| `\BenchVecBuildSumDynamicO` | 3.717 | `bench/results/summary.md: vec_build_sum n=4000 dynamic O median` |
| `\BenchListFoldN` | 32\,000 | `bench/results/summary.md: chosen size for list_fold` |
| `\BenchListFoldTypedCli` | 0.0654 | `bench/results/summary.md: list_fold n=32000 typed cli median` |
| `\BenchListFoldTypedO` | 0.0200 | `bench/results/summary.md: list_fold n=32000 typed O median` |
| `\BenchListFoldDynamicCli` | 0.0465 | `bench/results/summary.md: list_fold n=32000 dynamic cli median` |
| `\BenchListFoldDynamicO` | 0.0192 | `bench/results/summary.md: list_fold n=32000 dynamic O median` |
| `\BenchProtoSendN` | 4000 | `bench/results/summary.md: chosen size for proto_send` |
| `\BenchProtoSendTypedCli` | 0.0187 | `bench/results/summary.md: proto_send n=4000 typed cli median` |
| `\BenchProtoSendTypedO` | 0.0076 | `bench/results/summary.md: proto_send n=4000 typed O median` |
| `\BenchProtoSendDynamicCli` | 11.259 | `bench/results/summary.md: proto_send n=4000 dynamic cli median` |
| `\BenchProtoSendDynamicO` | 3.785 | `bench/results/summary.md: proto_send n=4000 dynamic O median` |
| `\BenchVecRevSumN` | 400 | `bench/results/summary.md: chosen size for vec_rev_sum` |
| `\BenchVecRevSumTypedCli` | 0.0672 | `bench/results/summary.md: vec_rev_sum n=400 typed cli median` |
| `\BenchVecRevSumTypedO` | 0.0228 | `bench/results/summary.md: vec_rev_sum n=400 typed O median` |
| `\BenchVecRevSumDynamicCli` | 15.072 | `bench/results/summary.md: vec_rev_sum n=400 dynamic cli median` |
| `\BenchVecRevSumDynamicO` | 4.455 | `bench/results/summary.md: vec_rev_sum n=400 dynamic O median` |
| `\BenchProofTypedCliRatio` | 1.31--1.32 | `bench/results/summary.md section 3: ratio of medians, typed cli` |
| `\BenchProofTypedCliNs` | 84--87 | `bench/results/summary.md section 3: extra ns per call, typed cli` |
| `\BenchProofTypedORatio` | 3.04--3.15 | `bench/results/summary.md section 3: ratio of medians, typed O` |
| `\BenchProofTypedONs` | 72 | `bench/results/summary.md section 3: extra ns per call, typed O` |
| `\BenchProofDynamicCliRatio` | 1.53--1.55 | `bench/results/summary.md section 3: ratio of medians, dynamic cli` |
| `\BenchProofDynamicCliNs` | 189--198 | `bench/results/summary.md section 3: extra ns per call, dynamic cli` |
| `\BenchProofDynamicORatio` | 1.56--1.68 | `bench/results/summary.md section 3: ratio of medians, dynamic O` |
| `\BenchProofDynamicONs` | 73--82 | `bench/results/summary.md section 3: extra ns per call, dynamic O` |
| `\BenchClosedIndexA` | 1.788 | `bench/results/summary.md section 5: closed index n=250` |
| `\BenchVarIndexA` | 0.7502 | `bench/results/summary.md section 5: variable index n=250` |
| `\BenchClosedIndexB` | 4.854 | `bench/results/summary.md section 5: closed index n=500` |
| `\BenchVarIndexB` | 0.7756 | `bench/results/summary.md section 5: variable index n=500` |
| `\BenchClosedIndexC` | 16.898 | `bench/results/summary.md section 5: closed index n=1000` |
| `\BenchVarIndexC` | 0.8127 | `bench/results/summary.md section 5: variable index n=1000` |
| `\BenchVarIndexRange` | 0.750--0.813 | `bench/results/summary.md section 5: minimum and maximum of the variable-index medians` |
| `\NumLeanLines` | 3419 | `cat mechanization/src/LRL.lean mechanization/src/LRL/Affine/Coercion.lean mechanization/src/LRL/Affine/Examples.lean mechanization/src/LRL/Affine/Ownership.lean mechanization/src/LRL/Affine/Semantics.lean mechanization/src/LRL/Affine/Substitution.lean mechanization/src/LRL/Affine/Syntax.lean mechanization/src/LRL/Affine/Typing.lean mechanization/src/LRL/Mechanized.lean mechanization/src/LRL/Metatheory.lean mechanization/src/LRL/Reduction.lean mechanization/src/LRL/Syntax.lean mechanization/src/LRL/Typing.lean | wc -l` |
| `\NumLeanFiles` | 13 | `files reachable from mechanization/src/LRL.lean by `import LRL...`` |
| `\NumAffineLines` | 2864 | `find mechanization/src/LRL/Affine -name '*.lean' -not -name '._*' -print0 | xargs -0 cat | wc -l` |
| `\NumAffineTheorems` | 126 | `cat mechanization/src/LRL/Affine/*.lean | grep -cE '^(theorem|lemma) '` |
| `\LeanToolchain` | v4.34.1 | `cat mechanization/lean-toolchain` |
| `\ToolLean` | 4.34.1 | `results_lean_idris.md header (lean --version)` |
| `\ToolIdris` | 0.8.0 | `results_lean_idris.md header (idris2 --version)` |
| `\ToolRustc` | 1.78.0 | `results_rust_racket.md header (rustc -vV)` |
| `\ToolRacket` | 9.3 | `results_rust_racket.md header (racket --version)` |
| `\NumStageProbeFiles` | 7 | `results_stage_matrix.md section 0, row 'dynamic | mir_gaps'` |
| `\BenchStackKiB` | 65\,520 | `bench/results/summary.md: machine block, ulimit -s` |
| `\BenchDynTypedRatioRange` | 195--899 | `bench/results/summary.md 'Ratios of medians': dynamic/typed (cli and O) for vec_build_sum 4000, proto_send 4000, vec_rev_sum 400` |
| `\PinnedCommit` | 7d2c91832b2237c6821870803681dac8387a0aba | `git rev-parse HEAD (clean artifact paths required)` |
| `\PinnedCommitShort` | 7d2c91832b | `git rev-parse HEAD (clean artifact paths required)` |
