# Statement correspondence: Erdős 1201 / JSP-001006

This project formalizes the natural **lower-density** statement for Erdős Problem 1201. Its target matches the [fixed FormalConjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/7d450ef6da7178b2716620e8492e26d0f8a9d81d/FormalConjectures/ErdosProblems/1201.lean).

For every real \(\epsilon>0\) and real \(\eta>0\), there is a natural number \(k\) such that

\[
\liminf_{N\to\infty}\frac1N
\#\left\{n\in\mathbb N: n<N,\quad
P^+\!\left(\prod_{i=0}^{k}(n+i)\right)>n^{1-\epsilon}\right\}
\ge1-\eta.
\]

## Exact formal scope

- **Full product:** `Finset.range (k + 1)` includes every factor from `n` through `n + k`. The threshold is the real power `(n : ℝ) ^ (1 - epsilon)` for each individual `n`.
- **All positive exponents:** `epsilon : ℝ` has only the assumption `0 < epsilon`. The proof uses `min epsilon (1/2)` as a stronger intermediate threshold, then transfers back to the original epsilon for every `n ≥ 1`. This includes epsilon greater than 1.
- **Fixed length:** `k` is chosen after epsilon and eta, before the limit variable `N`. It is independent of `N` and of the counted integer `n`.
- **All prefixes:** `Nat.count P N` counts the natural numbers in `[0,N)` satisfying `P`. The limit is along `(Filter.atTop : Filter ℕ)`, over all natural prefixes, rather than a selected subsequence. Dyadic estimates are transferred to arbitrary prefixes.
- **Lower density:** the ratio is embedded into `EReal` and its liminf is bounded below. The theorem does not assert existence of an ordinary natural-density limit or a density asymptotic.

The official target has `epsilon : ℝ` and **`eta : EReal`**, because eta occurs in `(1 - eta : EReal)`. The final theorem preserves this entire positive EReal range. For finite positive eta, the proof applies the real eventual bound to `eta.toReal`. For `eta = ⊤`, the requested lower bound is `⊥` and holds directly. A separate expanded theorem specializes eta to every positive real value by coercion.

`Erdos1201.lean:19–21,65–117` contains the exact set, the real eventual bound and the final EReal theorem. `VerifyOriginalStatement.lean:8–32` independently expands the official EReal target and its real-eta specialization, including the full product and prefix count.

## Zero and finite-prefix conventions

The prime-factor expression is exactly the official natural-number `sSup` of the set of prime divisors. At `n = 0`, the product is zero and this set is unbounded; the natural-number `sSup` convention gives zero. The positive-product argument is used only for `n > 0`. The transfer from intermediate prime witnesses to the target pays an explicit error of at most one counted point, which disappears after division by `N`. The proof eventually requires `N ≥ 1`, so the single value at `N = 0` does not affect the liminf. See `Erdos1201.lean:27–61,80–92`.

## Recorded verification and axioms

The audited proof sources passed `lake build JSP1006Proof` (9509 jobs), the independent expanded-statement check, and the official `leanchecker --verbose Erdos1201` replay, each with exit code 0. The replay checks the final module using its imported environment; it was run without `--fresh` and does not mean every imported dependency was replayed from scratch.

The four actual `#print axioms` outputs are:

| Theorem | Axiom dependencies |
|---|---|
| `Erdos1201.erdos_1201` | `propext`, `Classical.choice`, `Quot.sound` |
| `Erdos1201.erdos_1201_eventually` | `propext`, `Classical.choice`, `Quot.sound` |
| `audit_erdos1201_formalconjectures_statement` | `propext`, `Classical.choice`, `Quot.sound` |
| `audit_erdos1201_original_statement` | `propext`, `Classical.choice`, `Quot.sound` |

These are Lean's standard dependencies for this classical development. The accepted targets have no `sorryAx` or additional unproved mathematical axioms or hypothesis interfaces.

The successful audit uses **Lean 4.33.0** and Mathlib commit **`db584cd6d46c92f209a44c0f1c829460d327499d`**. The original archive requested Lean 4.33.1; it was explicitly changed to 4.33.0 to match the pinned dependency version. The verification records therefore certify the repaired 4.33.0 sources, not the original 4.33.1 configuration.

Audited `Erdos1201.lean` SHA256:

`B282388C18069BC400D527158CDD68CEEF9BDE9E1DB932EAAC02FC85A3EAD803`

## Mathematical provenance

The lower-density result is existing mathematics. The [1 May 2026 Ulam note, *The large-prime-divisor route to Erdős Problem #1201*](https://www.ulam.ai/research/erdos1201-lpd.pdf), Theorem 1.1 and Section 8, records the unconditional lower-density argument using the Matomäki–Radziwiłł theorem. This project contributes a checked Lean development of that scope, with a specialized analytic and prime-counting proof chain. It does not claim a new mathematical solution, priority over other formalizations, verification of a stronger density-limit assertion, or recognition of a prize award. Upstream formal proof contributions and their source provenance remain separately attributed.
