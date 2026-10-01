# Authorized repair build ledger

This is the authorized repaired candidate in `build/reference_4_33_0`, using Lean 4.33.0 and mathlib commit db584cd6d46c92f209a44c0f1c829460d327499d. The original ZIP and extracted reference_old remain unchanged. A 4.33.0 result is not acceptance of the original 4.33.1 configuration.

**Current final status: VERIFIED, proof sources frozen.** On 2026-10-01 at04:23:26 Asia/Shanghai, `021-full-final-ereal-order-explicit` naturally exited0 with `Build completed successfully (9509 jobs)`. The whole803-local-module dependency graph, including all31 root proof modules, passed. `022-independent-expanded-statements-four-axioms` naturally exited0 at04:24:08: both the explicit official positive EReal eta statement (includingtop) and its full positiveReal eta specialization were checked with the complete product and liminf written out. All FOUR actual axiom reports contain only `[propext, Classical.choice, Quot.sound]`. `023-official-leanchecker-final-module` naturally exited0 at04:25:30, replaying Erdos1201 using the official4.33.0 kernel checker. There are no active Lean/Lake/checker workers from this agent. Root now handles delivery metadata and final cache-reusing snapshot reproduction.

The repair policy preserves all original theorem statements and hypotheses. No sorry, axiom, admit, native_decide, or new assumption interface is permitted.

| Source | Actual observed failure | Minimal repair | Actual verification |
|---|---|---|---|
| ThetaLogPower.lean | Unknown Real.isLittleO_log_rpow_rpow_atTop; subsequent composition not simplified by Function.comp_apply | Use the global theorem; Function.comp_def in simpa only | 002-theta-comp-fixed: natural exit0 |
| RealTwoLengthComparison.lean | Global-namespace mismatch; bare function/composition not normalized by simpa | Remove Real.; eta-expand function by change; Function.comp_def | 015 log: module succeeded18s; standard three axioms |
| CofactorCounting.lean | rw could not match the unreduced product equality after pair destructuring; extra ring after closed field_simp goal | Definitional change of heq; remove redundant ring | 005 log: module succeeded17s |
| LongWindowDeficit.lean | Real.log_le_log endpoints unconstrained; reciprocal field identity not discharged by ring | Two explicit result types; field_simp before ring | 006 log: module succeeded22s |
| LongWindowUniform.lean | dsimp on already expanded expression; Real.log_le_log endpoints unconstrained; nlinarith side lemma had unknown cast target type | Remove dsimp; explicit log result type; explicit real cast lemma | 008-long-uniform-cast-fixed: natural exit0, entire window dependency target8834jobs |
| TruncationComparison.lean | normSq_natCast outputs product not pow2; sum_div direction wrong; redundant ring | Normalize pow_two; reverse sum_div; remove closed-goal ring | 010 log: module succeeded20s |
| PerronThreeBand.lean | Missing existing helper import; endpoint/measure/spatialX/length inference; integral function composition | Add existing helper import; annotate same existing implicit arguments; normalize composition; remove no-progress dsimp | 012 log: module succeeded19s |
| FarEnergyTransfer.lean | Indicator function argument unconstrained | Explicit existing normSq function argument | 013 log: module succeeded18s |
| ComparisonBudget.lean | gcongr split coefficient lost intended T squared bound; final field/factor arithmetic atom mismatch | Keep4 factor and use existing4*l^4 bound; explicit monotonicity calc; field_simp/ring | 014 log: module succeeded21s |
| OriginalThreshold.lean | normSq_ofReal product form differs from pow2 upper bound | Normalize with reverse pow_two | 016 log: module succeeded18s |
| DyadicBadWindows.lean | Euclidean-division product commutation; natural multiplication monotonicity; positive-factor cancellation API | simpa mul_comm; explicit Nat.mul_le_mul_right; positive right-factor iff | 017 log: module succeeded19s |
| DyadicDensity.lean | Dyadic endpoint powers not synchronized; Finset.filter DecidablePred instances differ; count arithmetic atoms | Simultaneous pow_succ; explicit convert/congr instance equality; same count expression then existing arithmetic | 019 log: module succeeded18s |
| Erdos1201.lean | Official eta:EReal passed to Real helper; final liminf type inference | Preserve original statement, split top/finite eta and lift via coe_toReal; explicitly type EReal liminf helper and coe_div normalization | 021 whole target natural exit0; 022 expanded statements/four axioms0; 023 module replay0 |

Each source has its immutable pre-repair backup, complete final diff, and change.json hashes in its numbered repair subdirectory. All iterations preserve full stdout/stderr and command metadata under build/.

## Historical build and recovery entries

The entries below describe earlier RUNNING, frozen, or failed phases. They are historical records, not the current final status given above. Failed Lean error-recovery output containing sorryAx was never accepted as verification evidence.

003-full-after-theta was deliberately stopped as a resource checkpoint after a measured Windows commit headroom near1GiB. It contains definite Cofactor source errors and an independent native/import resource failure. This is not a natural exit or a completed full build. Checkpoint metadata and process termination evidence are stored separately. Unchanged ErdosProblems.Erdos851.BetaChainRatio subsequently passed in single-thread004-beta-isolated, confirming that import/native failure was environmental. No third-party proof source was changed.

009-full-two-workers is the ongoing full-target repair build. Its actual final outcome must be recorded here after natural completion. Full theorem acceptance, independent expanded statement, final axiom reports, and optional checker replay remain pending.

## Live checkpoint 2026-10-01

The working proof sources are frozen while root creates a recovery snapshot. 009-full-two-workers remains active; no natural exit exists yet. Current command is `LEAN_NUM_THREADS=2 elan run leanprover/lean4:v4.33.0 lake build JSP1006Proof`, in the exact work tree recorded above. All observed small source errors up through008 are repaired and actually accepted in their targeted dependency builds. No unresolved source failure has yet occurred in009.

Actual success lines have been gathered in ROOT_SUCCESS_EVIDENCE.json for the root modules CofactorCounting, Elementary, LongWindowDeficit, LongWindowUniform, PrimeWindow, RealFarSeparation, ThetaLogPower. This evidence is not upgraded into final-theorem acceptance. The full803-module target remains active.

Recovery in the existing work tree must first check that no old Lake/Lean workers are still running; do not start a concurrent duplicate build. Keep all existing `.lake` dependency checkout and artifact caches. After a crash or deliberate stop, restart via run_build.ps1 with a fresh log label and `-Targets JSP1006Proof -Threads2`; Lake resumes from its persistent accepted-module checkpoint. Exact toolchain and pins remain the same. Continue until a natural whole-target success, then execute the expanded original statement and actual final axiom checks. Parent creates the deliverable snapshot only after source acceptance is complete.

Root checkpoint completed atomically at0226, CRC-tested and fsynced: checkpoints/JSP001006_RECOVERY_20261001_022615_385998.zip; SHA25695ebf04b65d5c7e839d5d9a30d20954595347602021f5d7e8231f3cced87ae38. The checkpoint includes825 source files,442/803 cached local modules, and105 audit files. Source freeze is released for further actual-error repairs;009 remains active.

Second durable checkpoint completed with full CRC pass: checkpoints/JSP001006_RECOVERY_20261001_025241_671401.zip; SHA256d87b1dc6a0649e23b9ee0efb74f468351c8ed0264510190f6280dd08900a6c80;825 source files,604 cached modules/4832cache files,116 audit files. Source freeze released;009 remains active with no new source failure.

Third durable checkpoint completed with full CRC pass and atomic fsync: checkpoints/JSP001006_RECOVERY_20261001_031629_966640.zip; SHA2569a183b03c5050985289296569b6146f21224bbbfbe95f31a245acd97952d7947;825 source files,767 cached modules/6136cache files,116 audit files. Source freeze released;009 remains active with no new source failure.

009 full target naturally exited1 after accepting all remaining reachable third-party/Far modules. The only failures were TruncationComparison and PerronThreeBand. Truncation's denominator normalization, sum_div direction, and redundant ring were minimally repaired and the module actually passed20s in010. Perron repairs fix the existing import for dyadicTwoLengthShortMeanSquareAt, explicit lower endpoint/volume, remove dsimp after change already unfolded it, and specify the same existing implicit spatialX in two helper calls. Before/after snapshots, final diff, hashes, and complete diagnostics are saved in numbered folders006/007. 010 naturally exited1 for these newly exposed Perron elaboration errors;011 now continues the full target with2workers. No mathematical statement or hypothesis was altered.

Fourth durable checkpoint completed with CRC/fsync/atomic pass: checkpoints/JSP001006_RECOVERY_20261001_034928_720522.zip; SHA256bb7ef78ccdb6a0d905d67fc53e343f0a0f72596860aa100c43d4b8a5d6fd8c6f;825 source,798 accepted cached modules/6384cache files,148 audit files. 014 naturally exited1 after ComparisonBudget actually passed21s; RealTwoLengthComparison's two function-form normalization errors remain. Source freeze released. Final independent verification now requires BOTH the explicit official EReal-eta statement (includingtop) and the positiveReal-eta mathematical specialization, plus FOUR actual axiom outputs. Failed error-recovery axiom outputs containing sorryAx are not accepted evidence.
