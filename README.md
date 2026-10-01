# JSP-001006 / Erdős 1201 in Lean

This project proves the full lower-natural-density formulation of Erdős problem 1201. For every real `epsilon > 0` and real `eta > 0`, there is a fixed integer `k` such that the lower density of

\[
\{n\in\mathbb N:P(n(n+1)\cdots(n+k))>n^{1-\epsilon}\}
\]

is at least `1 - eta`. Here `P` is represented by the supremum in `ℕ` of the prime divisors of the complete product. The theorem `Erdos1201.erdos_1201` also covers the positive `EReal` value of `eta` used by the reference formal statement, including `eta = ⊤`.

This is a formalization contribution. The lower-density mathematical argument was publicly posted by Przemek Chojecki on 30 April 2026 and is treated unconditionally in §8 of the [1 May 2026 note](https://www.ulam.ai/research/erdos1201-lpd.pdf), including its Theorem 1.1. The project does not claim a new mathematical solution or proof that the ordinary density limit exists. The stronger density-existence discussion in that note uses additional hypotheses and is not used as an assumption here.

The problem appears in Erdős, [*A survey of problems in combinatorial number theory*](https://www.renyi.hu/~p_erdos/1980-03.pdf), printed page 107, problem 2. The proposed formal statement follows [FormalConjectures at commit `137aec5c7abd3aa61f7a73138a97279acfc79e93`](https://github.com/google-deepmind/formal-conjectures/blob/137aec5c7abd3aa61f7a73138a97279acfc79e93/FormalConjectures/ErdosProblems/1201.lean), subject to award-maintainer review.

## Proof and coverage

- `Erdos1201.erdos_1201`: full positive real `epsilon`, full positive `EReal eta`, and the `liminf` density bound.
- `Erdos1201.erdos_1201_eventually`: the stronger eventual count bound for positive real `epsilon` and `eta`.
- `VerifyOriginalStatement.lean`: separately elaborates the fully expanded reference statement and its positive-real-`eta` specialization. It uses the actual product and count expression, rather than a replacement assumption.

The integer `k` is chosen before the limit variable. The product includes shifts `0, …, k`. `Nat.count` counts `0 ≤ n < N`; the single exceptional start `n = 0` is paid explicitly by a count error of at most one. Restricting an intermediate exponent to `min epsilon (1/2)` proves a stronger intermediate assertion and does not restrict the final theorem's quantifiers.

## Version and dependencies

| Component | Fixed version |
| --- | --- |
| Lean | `leanprover/lean4:v4.33.0` |
| Lean release commit | `d8b18978322de05a8f3dba51ef03cf5461676c17` |
| mathlib4 | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| plby/lean-proofs | `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` |
| frenzymath/FormalPantheon | `ffbb65c21afc8a36ace67720f1b0df1c63d26bd1` |

The supplied draft requested Lean 4.33.1. The repaired and verified project uses 4.33.0, matching the pinned dependencies and upstream compatibility patches. Verification of the original 4.33.1 draft is not claimed. The original archive was retained unchanged locally; the version change and proof repairs are documented in the verification evidence.

## Repository boundary and attribution

The public repository records the submitted integration and additional proof modules, reproduction tooling, source references, hashes and verification evidence. The bootstrap downloads the pinned upstream sources and creates eleven localized `Far*.lean` modules in the local checkout. Downloaded and generated third-party files are excluded from Git. See `ATTRIBUTION.md` for the exact file boundary and authorship distinctions.

Upstream authorship and source notices are retained. Exact source revisions, file hashes and localized adaptations are documented in `external-sources.json` and `ATTRIBUTION.md`.

Some accepted proof files retain historical `UNCOMPILED DRAFT` comments from the input archive. They describe the original draft, not the later verification result. The immutable proof-source hashes and the recorded commands determine the checked version.

## Reproduction

Proof repository: https://github.com/peilinliu66-dev/jsp1006-erdos1201-formalization; branch `codex/jsp1006`. The immutable full commit is recorded in the award submission. Run `git rev-parse HEAD` to identify your checkout.

Requirements: Git, Python 3.10 or later, Elan/Lake on `PATH`, and network access to the pinned upstream sources and Lean dependencies. Start with a fresh checkout of the selected commit:

```text
python -X utf8 fetch_sources.py
python -X utf8 verify_project.py --project . --threads 2
```

`fetch_sources.py` verifies downloaded-source and generated-file hashes against the accepted proof snapshot and fails on a mismatch. `verify_project.py` records the executed Lean version, obtains the official mathlib cache, builds `JSP1006Proof`, checks the independent statement and all four axiom reports, and records real outputs under `verification_logs/`. If the cache is already present, `--skip-cache` skips the download. The underlying target commands are `lake build JSP1006Proof` and `lake env lean VerifyOriginalStatement.lean` under the pinned toolchain.

The supplemental kernel replay is a separate command:

```text
elan run leanprover/lean4:v4.33.0 lake env leanchecker --verbose Erdos1201
```

A fresh checkout provides the clean setup procedure; official dependency caches may be downloaded. The publication agent's local check may reuse the accepted `.lake` cache after comparing every local proof source byte for byte. Such a run checks the new public layout and statement entry but is not an empty-cache rebuild on another machine. The reproduction report must identify which procedure was actually executed.

## Verified local result and trust dependencies

The repaired local snapshot completed `lake build JSP1006Proof` with exit code 0 on 1 October 2026, producing `Build completed successfully (9509 jobs).` All 31 root modules and the 803 local source files in the checked import closure were accepted. The independent expanded-statement check and the official final-module `leanchecker` replay also exited 0.

Actual output from `VerifyOriginalStatement.lean`:

```text
'audit_erdos1201_formalconjectures_statement' depends on axioms: [propext, Classical.choice, Quot.sound]
'audit_erdos1201_original_statement' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1201.erdos_1201' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1201.erdos_1201_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` or added problem-specific unproved axiom appears in those dependencies. The `leanchecker` replay checked the final `Erdos1201` module using its imported environment. It did not use `--fresh`, did not independently replay the entire dependency closure, skipped unsafe/partial declarations according to the tool's behavior, and permitted axiom declarations; the separate axiom reports above are therefore part of the evidence.

Accepted source SHA-256 values:

```text
Erdos1201.lean: b282388c18069bc400d527158cdd68ceef9bde9e1db932eaac02fc85a3ead803
VerifyOriginalStatement.lean: e8ecd9e09e4f347a6ee4137180bccde6ed13763bfb8ae6cc77a9bebd1c741ae9
```

Public bootstrap and publication-directory reproduction are recorded in `verification/publication-summary.json` and their accompanying logs. The original acceptance logs and the later publication-directory logs are distinguished explicitly; matching proof hashes bind both to the same proof sources.

Award submission and acceptance are separate. The mathematical source, statement correspondence and formalization contribution are supplied for maintainer review. No award approval or priority claim is inferred from the local build result.

The publication directory also passed the complete build and all four axiom checks with the existing accepted cache. A fresh network bootstrap reconstructed every selected external input and adaptation with identical SHA-256 values. See [publication verification](verification/publication-summary.json).
