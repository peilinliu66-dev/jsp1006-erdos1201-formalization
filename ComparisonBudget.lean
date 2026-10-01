/- Explicit cutoff and scalar budget for the real two-length comparison.
   UNCOMPILED DRAFT. No mean-square hypothesis is introduced here. -/
import FarEnergyTransfer
import TruncationComparison
import LongWindowUniform

open scoped Classical

open Filter MeasureTheory
open scoped BigOperators Interval Topology
open Erdos67b

namespace JSP1006
noncomputable section

def comparisonTailCost (c : ℝ) : ℝ :=
  4096 * lemma14UniversalScaledHighConstant * (1 / c + Real.pi / c ^ 2)

def comparisonVanishingCost (X : ℕ) : ℝ :=
  2048 * ‖(((2 * Real.pi : ℝ) : ℂ))⁻¹‖ ^ 2 / Real.log (X : ℝ) ^ 24 +
    16 / Real.log (X : ℝ) ^ 16

theorem comparisonTailCost_nonneg {c : ℝ} (hc : 0 < c) : 0 ≤ comparisonTailCost c := by
  unfold comparisonTailCost
  exact mul_nonneg (mul_nonneg (by norm_num) lemma14UniversalScaledHighConstant_nonneg)
    (by positivity)

/-- Quantitative scalar bound at the actual short/long and near/far cutoffs. -/
theorem twoLengthEnergy_le_explicit_budget
    (blocks : Finset (ℕ × ℕ)) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1) {X H : ℕ}
    (hH : 0 < H) (hHL : H ≤ longLength X) (hLX : longLength X ≤ X)
    (hlog : 1 ≤ Real.log (X : ℝ)) {c epsilon delta : ℝ} (hc : 0 < c)
    (hepsilon : 0 ≤ epsilon) (hdelta : 0 ≤ delta)
    (hcut : 1 + Real.log (X : ℝ) ^ 2 ≤ c * X)
    (hdensity : ((atypicalFactorizationSet blocks (3 * X)).card : ℝ) ≤ delta * X)
    (henergy : (∫ t in -(c * X)..(c * X), (farFrequencySet X).indicator
      (fun t => ‖mrTypicalDyadicPolynomial blocks f X t‖ ^ 2) t) ≤ epsilon) :
    twoLengthEnergy f X H (longLength X) ≤
      (comparisonVanishingCost X + 256 * lemma14UniversalScaledLowConstant * epsilon +
        16 * delta + comparisonTailCost c / (H : ℝ) ^ 2) * X := by
  let L := longLength X
  let l := Real.log (X : ℝ)
  let T := 1 + l ^ 2
  let U := c * (X : ℝ)
  let S := typicalFactorizationSet blocks (3 * X)
  let K := ‖(((2 * Real.pi : ℝ) : ℂ))⁻¹‖
  have hL : 0 < L := lt_of_lt_of_le hH hHL
  have hX : 0 < X := lt_of_lt_of_le hL hLX
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hXone : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hHLR : (H : ℝ) ≤ L := by exact_mod_cast hHL
  have hl : 0 < l := lt_of_lt_of_le zero_lt_one hlog
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hU : 0 < U := mul_pos hc hXR
  have hfloor : (L : ℝ) ≤ (X : ℝ) / l ^ 16 := Nat.floor_le (by positivity)
  have hTle : T ≤ 2 * l ^ 2 := by
    have hh : 1 ≤ l ^ 2 := one_le_pow₀ hlog
    dsimp [T]; linarith
  have hT2 : T ^ 2 ≤ 4 * l ^ 4 := by
    have hh := pow_le_pow_left₀ hT hTle 2
    nlinarith only [hh]
  have hratio : 2 * T ^ 2 * ((H : ℝ) + L) / ((X : ℝ) + 1) ≤ 16 / l ^ 12 := by
    calc
      _ ≤ 4 * T ^ 2 * L / (X : ℝ) := by
        apply (div_le_div_iff₀ (by positivity) hXR).mpr
        have h₁ := mul_le_mul_of_nonneg_left (show (H : ℝ) + L ≤ 2 * L by linarith)
          (by positivity : 0 ≤ 2 * T ^ 2 * (X : ℝ))
        nlinarith [mul_nonneg (sq_nonneg T) hLR.le]
      _ ≤ 4 * (4 * l ^ 4) * ((X : ℝ) / l ^ 16) / (X : ℝ) := by
        gcongr
      _ = 16 / l ^ 12 := by field_simp [hl.ne', hXR.ne'] <;> ring
  have hcentral : 4 * ((X : ℝ) *
      (K * (2 * T ^ 2 * ((H : ℝ) + L) / ((X : ℝ) + 1))) ^ 2) ≤
      1024 * K ^ 2 * X / l ^ 24 := by
    calc
      _ ≤ 4 * ((X : ℝ) * (K * (16 / l ^ 12)) ^ 2) := by
        gcongr
      _ = _ := by field_simp; ring
  have hF : Continuous (dyadicVerticalDirichletPolynomial S f X) :=
    continuous_dyadicVerticalDirichletPolynomial S f X
  have hfar : (∫ t in -U..U, (farFrequencySet X).indicator
      (fun t => Complex.normSq (dyadicVerticalDirichletPolynomial S f X t)) t) ≤ epsilon := by
    rw [integral_far_dyadic_typical_eq blocks f (by omega : 2 * X ≤ 3 * X)]
    exact henergy
  have hmiddle := middle_energy_le_twice_far hF hU.le hcut hfar
  have hlow := lemma14UniversalScaledLowConstant_nonneg
  have hhigh := lemma14UniversalScaledHighConstant_nonneg
  have hm : 32 * lemma14UniversalScaledLowConstant * ((X : ℝ) + 1) *
      ((∫ t in -U..-T, Complex.normSq (dyadicVerticalDirichletPolynomial S f X t)) +
        ∫ t in T..U, Complex.normSq (dyadicVerticalDirichletPolynomial S f X t)) ≤
      128 * lemma14UniversalScaledLowConstant * epsilon * X := by
    calc
      _ ≤ 32 * lemma14UniversalScaledLowConstant * ((X : ℝ) + 1) * (2 * epsilon) := by
        gcongr
      _ ≤ 32 * lemma14UniversalScaledLowConstant * (2 * (X : ℝ)) * (2 * epsilon) := by
        gcongr; linarith
      _ = _ := by ring
  let coeff h := lemma14UniversalPerronSegmentSafeWeightedCoefficient
    ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) h
  have hcH := lemma14UniversalPerronSegmentSafeWeightedCoefficient_shifted_le hH (hHL.trans hLX)
  have hcL := lemma14UniversalPerronSegmentSafeWeightedCoefficient_shifted_le hL hLX
  have hcoeff : coeff H + coeff L ≤
      16 * lemma14UniversalScaledHighConstant * (X : ℝ) ^ 3 / (H : ℝ) ^ 2 := by
    have hxplus : ((X : ℝ) + 1) ^ 3 ≤ 8 * (X : ℝ) ^ 3 := by
      have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (X : ℝ) + 1)
        (by linarith : (X : ℝ) + 1 ≤ 2 * X) 3
      nlinarith only [hh]
    have hden : (H : ℝ) ^ 2 ≤ (L : ℝ) ^ 2 := pow_le_pow_left₀ hHR.le hHLR 2
    have hcL' : coeff L ≤ lemma14UniversalScaledHighConstant * ((X : ℝ) + 1) ^ 3 / (H : ℝ) ^ 2 := by
      refine hcL.trans ?_
      exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hHR) hden
    have hcH' : coeff H ≤ lemma14UniversalScaledHighConstant * ((X : ℝ) + 1) ^ 3 / (H : ℝ) ^ 2 := hcH
    calc
      _ ≤ 2 * (lemma14UniversalScaledHighConstant * ((X : ℝ) + 1) ^ 3 / (H : ℝ) ^ 2) := by linarith
      _ ≤ 2 * (lemma14UniversalScaledHighConstant * (8 * (X : ℝ) ^ 3) / (H : ℝ) ^ 2) := by gcongr
      _ = _ := by ring
  have htail : 8 * (coeff H + coeff L) *
      (16 / ((X : ℝ) * U) + 16 * Real.pi / U ^ 2) ≤
      (comparisonTailCost c / 2) * X / (H : ℝ) ^ 2 := by
    calc
      _ ≤ 8 * (16 * lemma14UniversalScaledHighConstant * (X : ℝ) ^ 3 / (H : ℝ) ^ 2) *
          (16 / ((X : ℝ) * U) + 16 * Real.pi / U ^ 2) := by gcongr
      _ = _ := by dsimp [comparisonTailCost, U]; field_simp; ring
  have hdyadic := dyadic_twoLength_threeBand S hf hX hH hL (hHL.trans hLX) hLX hT hU hcut
  have hfull := twoLengthEnergy_le_dyadic_add_errors blocks hf hH hL (hHL.trans hLX) hLX
  have hboundary : (8 : ℝ) * (H + L : ℕ) ≤ 16 * (X : ℝ) / l ^ 16 := by
    push_cast
    calc
      8 * ((H : ℝ) + L) ≤ 16 * L := by linarith
      _ ≤ 16 * ((X : ℝ) / l ^ 16) := by gcongr
      _ = _ := by ring
  have hD : dyadicTwoLengthShortMeanSquareAt S f X X H L ≤
      1024 * K ^ 2 * X / l ^ 24 +
      128 * lemma14UniversalScaledLowConstant * epsilon * X +
      (comparisonTailCost c / 2) * X / (H : ℝ) ^ 2 := by
    change dyadicTwoLengthShortMeanSquareAt S f X X H L ≤ _ at hdyadic
    change 8 * (coeff H + coeff L) * _ ≤ _ at htail
    linarith
  change twoLengthEnergy f X H L ≤ _
  calc
    twoLengthEnergy f X H L ≤
        2 * dyadicTwoLengthShortMeanSquareAt S f X X H L +
          16 * ((atypicalFactorizationSet blocks (3 * X)).card : ℝ) +
          8 * ((H + L : ℕ) : ℝ) := hfull
    _ ≤ 2 * (1024 * K ^ 2 * X / l ^ 24 +
          128 * lemma14UniversalScaledLowConstant * epsilon * X +
          (comparisonTailCost c / 2) * X / (H : ℝ) ^ 2) +
          16 * (delta * X) + 16 * (X : ℝ) / l ^ 16 := by
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left hD (by norm_num : (0 : ℝ) ≤ 2))
          (mul_le_mul_of_nonneg_left hdensity (by norm_num : (0 : ℝ) ≤ 16)))
        hboundary
    _ = (comparisonVanishingCost X +
          256 * lemma14UniversalScaledLowConstant * epsilon +
          16 * delta + comparisonTailCost c / (H : ℝ) ^ 2) * X := by
      dsimp only [comparisonVanishingCost, l, K]
      ring

end
end JSP1006
