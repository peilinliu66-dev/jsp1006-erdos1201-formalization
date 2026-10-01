/- Finite L2 comparison with a single dyadic truncation. UNCOMPILED DRAFT. -/
import ErdosProblems.Erdos67b.MRTypicalShortBoundary
import ErdosProblems.Erdos67b.MRLemma14TwoLengthSplitAt

open scoped Classical

open scoped BigOperators
open Erdos67b

namespace JSP1006
noncomputable section

def shortAverage (f : ℕ → ℂ) (n H : ℕ) : ℂ :=
  (∑ j ∈ Finset.Icc 1 H, f (n + j)) / (H : ℂ)

def twoLengthEnergy (f : ℕ → ℂ) (X H L : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq (shortAverage f n H - shortAverage f n L)

theorem shortAverage_dyadic (S : Finset ℕ) (f : ℕ → ℂ) (X n H : ℕ) :
    shortAverage (dyadicRestrictedCoefficient S f X) n H =
      dyadicRestrictedShortAverage S f X n H := by
  rw [shortAverage, dyadicRestrictedShortAverage, sum_Icc_add_eq_sum_Ioc]

/-- This estimates the difference, rather than merely the energy of the two sums. -/
theorem sum_normSq_typical_sub_dyadic_le_boundary
    (blocks : Finset (ℕ × ℕ)) (Z : ℕ) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1) (X H : ℕ) :
    (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq
      (typicalModulatedShortSum blocks Z f n H 0 -
        ∑ j ∈ Finset.Icc 1 H,
          dyadicRestrictedCoefficient (typicalFactorizationSet blocks Z) f X (n + j))) ≤
        (H : ℝ) ^ 3 := by
  classical
  let S := typicalFactorizationSet blocks Z
  let g := dyadicRestrictedCoefficient S f X
  let B := Finset.Ioc (2 * X - H) (2 * X)
  have hcard : B.card ≤ H := by dsimp [B]; simp only [Nat.card_Ioc]; omega
  have hpoint (n : ℕ) (hn : n ∈ Finset.Ioc X (2 * X)) :
      Complex.normSq (typicalModulatedShortSum blocks Z f n H 0 -
        ∑ j ∈ Finset.Icc 1 H, g (n + j)) ≤
          if n ∈ B then (H : ℝ) ^ 2 else 0 := by
    by_cases hinside : n + H ≤ 2 * X
    · have heq : typicalModulatedShortSum blocks Z f n H 0 =
          ∑ j ∈ Finset.Icc 1 H, g (n + j) := by
        unfold typicalModulatedShortSum
        apply Finset.sum_congr rfl
        intro j hj
        have hn' := Finset.mem_Ioc.mp hn
        have hj' := Finset.mem_Icc.mp hj
        have hmem : n + j ∈ Finset.Ioc X (2 * X) := Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
        simp [g, S, dyadicRestrictedCoefficient, dyadicRestrictedSupport, hmem, additivePhase]
      rw [heq, sub_self, Complex.normSq_zero]
      positivity
    · have hnB : n ∈ B := by
        have hn' := Finset.mem_Ioc.mp hn
        exact Finset.mem_Ioc.mpr ⟨by omega, hn'.2⟩
      have hterm (j : ℕ) (hj : j ∈ Finset.Icc 1 H) :
          ‖(if n + j ∈ S then f (n + j) else 0) - g (n + j)‖ ≤ 1 := by
        have hj0 := (Finset.mem_Icc.mp hj).1
        by_cases hs : n + j ∈ S <;> by_cases hd : n + j ∈ Finset.Ioc X (2 * X)
        · simp [g, dyadicRestrictedCoefficient, dyadicRestrictedSupport, hs, hd]
        · simpa [g, dyadicRestrictedCoefficient, dyadicRestrictedSupport, hs, hd] using
            hf (n + j) (by omega)
        · simp [g, dyadicRestrictedCoefficient, dyadicRestrictedSupport, hs, hd]
        · simp [g, dyadicRestrictedCoefficient, dyadicRestrictedSupport, hs, hd]
      have hnorm : ‖typicalModulatedShortSum blocks Z f n H 0 -
          ∑ j ∈ Finset.Icc 1 H, g (n + j)‖ ≤ (H : ℝ) := by
        calc
          _ = ‖∑ j ∈ Finset.Icc 1 H,
              ((if n + j ∈ S then f (n + j) else 0) - g (n + j))‖ := by
            simp [typicalModulatedShortSum, S, additivePhase, Finset.sum_sub_distrib]
          _ ≤ ∑ j ∈ Finset.Icc 1 H,
              ‖(if n + j ∈ S then f (n + j) else 0) - g (n + j)‖ := norm_sum_le _ _
          _ ≤ ∑ _j ∈ Finset.Icc 1 H, (1 : ℝ) := Finset.sum_le_sum hterm
          _ = _ := by simp
      rw [if_pos hnB, Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hcount : ((Finset.Ioc X (2 * X)).filter (· ∈ B)).card ≤ H := by
    refine (Finset.card_le_card ?_).trans hcard
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  calc
    _ ≤ ∑ n ∈ Finset.Ioc X (2 * X), if n ∈ B then (H : ℝ) ^ 2 else 0 :=
      Finset.sum_le_sum hpoint
    _ = (((Finset.Ioc X (2 * X)).filter (· ∈ B)).card : ℝ) * (H : ℝ) ^ 2 := by
      rw [← Finset.sum_filter]; simp
    _ ≤ (H : ℝ) * (H : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (sq_nonneg _)
    _ = _ := by ring

/-- After normalization the atypical loss is its cardinality, and the endpoint loss is H. -/
theorem sum_normSq_shortAverage_sub_dyadic_le
    (blocks : Finset (ℕ × ℕ)) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1) {X H : ℕ}
    (hH : 0 < H) (hHX : H ≤ X) :
    (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq
      (shortAverage f n H -
        dyadicRestrictedShortAverage (typicalFactorizationSet blocks (3 * X)) f X n H)) ≤
      2 * ((atypicalFactorizationSet blocks (3 * X)).card : ℝ) + 2 * H := by
  classical
  let S := typicalFactorizationSet blocks (3 * X)
  let g := dyadicRestrictedCoefficient S f X
  let E (n : ℕ) := modulatedShortSum f n H 0 - typicalModulatedShortSum blocks (3 * X) f n H 0
  let B (n : ℕ) := typicalModulatedShortSum blocks (3 * X) f n H 0 -
    ∑ j ∈ Finset.Icc 1 H, g (n + j)
  have hE := sum_Ioc_normSq_modulatedShortSum_sub_typical_le
    (blocks := blocks) (Z := 3 * X) (X := X) (H := H) (alpha := 0)
    (by intro n hn j hj; have hn' := (Finset.mem_Icc.mp hn).2
        have hj' := (Finset.mem_Icc.mp hj).2; omega) hf
  have hB := sum_normSq_typical_sub_dyadic_le_boundary blocks (3 * X) hf X H
  have hH0 : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have hHsq : 0 < (H : ℝ) ^ 2 := sq_pos_of_ne_zero hH0
  have hpoint (n : ℕ) :
      Complex.normSq (shortAverage f n H - dyadicRestrictedShortAverage S f X n H) ≤
      (2 * Complex.normSq (E n) + 2 * Complex.normSq (B n)) / (H : ℝ) ^ 2 := by
    have heq : shortAverage f n H - dyadicRestrictedShortAverage S f X n H =
        (E n + B n) / (H : ℂ) := by
      rw [← shortAverage_dyadic]
      simp only [shortAverage, E, B, modulatedShortSum_zero, g]
      ring
    rw [heq, Complex.normSq_div, Complex.normSq_natCast, ← pow_two]
    exact div_le_div_of_nonneg_right (normSq_add_le_two_mul _ _) hHsq.le
  calc
    _ ≤ ∑ n ∈ Finset.Ioc X (2 * X),
        (2 * Complex.normSq (E n) + 2 * Complex.normSq (B n)) / (H : ℝ) ^ 2 :=
      Finset.sum_le_sum (fun n _ => hpoint n)
    _ = (2 * (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq (E n)) +
        2 * (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq (B n))) / (H : ℝ) ^ 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (2 * ((H : ℝ) ^ 2 * (atypicalFactorizationSet blocks (3 * X)).card) +
        2 * (H : ℝ) ^ 3) / (H : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ hHsq.le
      change (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq (E n)) ≤ _ at hE
      change (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq (B n)) ≤ _ at hB
      linarith
    _ = _ := by field_simp

/-- Both lengths use the SAME ambient mask and dyadic polynomial. -/
theorem twoLengthEnergy_le_dyadic_add_errors
    (blocks : Finset (ℕ × ℕ)) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1) {X H L : ℕ}
    (hH : 0 < H) (hL : 0 < L) (hHX : H ≤ X) (hLX : L ≤ X) :
    twoLengthEnergy f X H L ≤
      2 * dyadicTwoLengthShortMeanSquareAt (typicalFactorizationSet blocks (3 * X)) f X X H L +
      16 * ((atypicalFactorizationSet blocks (3 * X)).card : ℝ) + 8 * (H + L : ℕ) := by
  let S := typicalFactorizationSet blocks (3 * X)
  let A n := shortAverage f n H - dyadicRestrictedShortAverage S f X n H
  let B n := shortAverage f n L - dyadicRestrictedShortAverage S f X n L
  let D n := dyadicRestrictedShortAverage S f X n H - dyadicRestrictedShortAverage S f X n L
  have hp (n : ℕ) : Complex.normSq (shortAverage f n H - shortAverage f n L) ≤
      2 * Complex.normSq (D n) + 4 * Complex.normSq (A n) + 4 * Complex.normSq (B n) := by
    have heq : shortAverage f n H - shortAverage f n L = D n + (A n - B n) := by
      dsimp [D, A, B]; ring
    rw [heq]
    have h₁ := normSq_add_le_two_mul (D n) (A n - B n)
    have h₂ := normSq_sub_le_two_mul_add (A n) (B n)
    linarith
  have hs := Finset.sum_le_sum (s := Finset.Ioc X (2 * X)) (fun n _ => hp n)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have h₁ := sum_normSq_shortAverage_sub_dyadic_le blocks hf hH hHX
  have h₂ := sum_normSq_shortAverage_sub_dyadic_le blocks hf hL hLX
  change twoLengthEnergy f X H L ≤ 2 * dyadicTwoLengthShortMeanSquareAt S f X X H L +
    4 * (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq (A n)) +
    4 * (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq (B n)) at hs
  change (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq (A n)) ≤ _ at h₁
  change (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq (B n)) ≤ _ at h₂
  push_cast
  linarith

end
end JSP1006
