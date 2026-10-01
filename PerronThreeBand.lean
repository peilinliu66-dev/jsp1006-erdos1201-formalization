/-
Three-frequency-band, two-length comparison. UNCOMPILED DRAFT.
The middle band uses the unweighted O(X) Perron L2 bound; only the outer
tail uses the reciprocal-square bound. This distinction prevents a false
X^3/H^2 loss at the small central cutoff.
-/
import ErdosProblems.Erdos67b.MRLemma14DyadicTail
import ErdosProblems.Erdos67b.MRLemma14TwoLengthSplitAt

open scoped Classical

open MeasureTheory
open scoped Interval
open Erdos67b

namespace JSP1006

noncomputable section

def perronDifference (F : ℝ → ℂ) (H₁ H₂ A B x : ℝ) : ℂ :=
  perronKernelSegmentOn F x H₁ A B - perronKernelSegmentOn F x H₂ A B

def perronDifferenceEnergy (X : ℕ) (F : ℝ → ℂ) (H₁ H₂ A B : ℝ) : ℝ :=
  ∫ x in ((X : ℝ) + 1)..(((2 * X : ℕ) : ℝ) + 1),
    Complex.normSq (perronDifference F H₁ H₂ A B x)

theorem perronSegment_continuousOn_window
    (F : ℝ → ℂ) (hF : Continuous F) (X : ℕ) {H : ℝ} (hH : 0 < H) (A B : ℝ) :
    ContinuousOn (fun x => perronKernelSegmentOn F x H A B)
      (Set.uIcc ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1)) := by
  have hPQ : (X : ℝ) + 1 ≤ ((2 * X : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show X + 1 ≤ 2 * X + 1 by omega)
  exact (continuousOn_perronKernelSegmentOn F hF (P := (X : ℝ) + 1)
    (by positivity) hH A B).mono
    (by rw [Set.uIcc_of_le hPQ]; intro x hx; exact hx.1)

theorem perronDifference_continuousOn_window
    (F : ℝ → ℂ) (hF : Continuous F) (X : ℕ)
    {H₁ H₂ : ℝ} (hH₁ : 0 < H₁) (hH₂ : 0 < H₂) (A B : ℝ) :
    ContinuousOn (perronDifference F H₁ H₂ A B)
      (Set.uIcc ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1)) :=
  (perronSegment_continuousOn_window F hF X hH₁ A B).sub
    (perronSegment_continuousOn_window F hF X hH₂ A B)

theorem normSq_three_le (a b c : ℂ) :
    Complex.normSq (a + b + c) ≤
      2 * Complex.normSq a + 4 * Complex.normSq b + 4 * Complex.normSq c := by
  have h₁ := normSq_sub_le_two_mul_add a (-(b + c))
  have h₂ := normSq_sub_le_two_mul_add b (-c)
  simp only [sub_neg_eq_add, Complex.normSq_neg] at h₁ h₂
  have heq : a + b + c = a + (b + c) := by ring
  rw [heq]
  linarith

theorem perronDifference_split (F : ℝ → ℂ) (hF : Continuous F)
    {x H₁ H₂ : ℝ} (hx : 0 < x) (hH₁ : 0 < H₁) (hH₂ : 0 < H₂) (T U : ℝ) :
    perronDifference F H₁ H₂ (-U) U x =
      perronDifference F H₁ H₂ (-T) T x +
      perronDifference F H₁ H₂ (-U) (-T) x +
      perronDifference F H₁ H₂ T U x := by
  unfold perronDifference
  rw [perronKernelSegmentOn_eq_central_add_symmetricHigh F hF hx hH₁,
    perronKernelSegmentOn_eq_central_add_symmetricHigh F hF hx hH₂]
  unfold lemma14SymmetricPerronHighSegmentOn
  ring

theorem perronDifferenceEnergy_split_le
    (F : ℝ → ℂ) (hF : Continuous F) (X : ℕ)
    {H₁ H₂ : ℝ} (hH₁ : 0 < H₁) (hH₂ : 0 < H₂) (T U : ℝ) :
    perronDifferenceEnergy X F H₁ H₂ (-U) U ≤
      2 * perronDifferenceEnergy X F H₁ H₂ (-T) T +
      4 * perronDifferenceEnergy X F H₁ H₂ (-U) (-T) +
      4 * perronDifferenceEnergy X F H₁ H₂ T U := by
  let P : ℝ := X + 1
  let Q : ℝ := (2 * X : ℕ) + 1
  have hPQ : P ≤ Q := by dsimp [P, Q]; exact_mod_cast (show X + 1 ≤ 2 * X + 1 by omega)
  have hi (A B : ℝ) : IntervalIntegrable
      (fun x => Complex.normSq (perronDifference F H₁ H₂ A B x)) volume P Q :=
    (Complex.continuous_normSq.comp_continuousOn
      (perronDifference_continuousOn_window F hF X hH₁ hH₂ A B)).intervalIntegrable
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc P Q) :
      Complex.normSq (perronDifference F H₁ H₂ (-U) U x) ≤
        2 * Complex.normSq (perronDifference F H₁ H₂ (-T) T x) +
        4 * Complex.normSq (perronDifference F H₁ H₂ (-U) (-T) x) +
        4 * Complex.normSq (perronDifference F H₁ H₂ T U x) := by
    have hx0 : 0 < x := lt_of_lt_of_le (by dsimp [P]; positivity) hx.1
    rw [perronDifference_split F hF hx0 hH₁ hH₂ T U]
    exact normSq_three_le _ _ _
  have hm := intervalIntegral.integral_mono_on hPQ (hi (-U) U)
    (((hi (-T) T).const_mul 2).add ((hi (-U) (-T)).const_mul 4) |>.add ((hi T U).const_mul 4)) hpoint
  unfold perronDifferenceEnergy
  change (∫ x in P..Q, _) ≤ _
  calc
    _ ≤ ∫ x in P..Q,
        (2 * Complex.normSq (perronDifference F H₁ H₂ (-T) T x) +
        4 * Complex.normSq (perronDifference F H₁ H₂ (-U) (-T) x) +
        4 * Complex.normSq (perronDifference F H₁ H₂ T U x)) := hm
    _ = _ := by
      rw [intervalIntegral.integral_add
        (((hi (-T) T).const_mul 2).add ((hi (-U) (-T)).const_mul 4)) ((hi T U).const_mul 4),
        intervalIntegral.integral_add ((hi (-T) T).const_mul 2) ((hi (-U) (-T)).const_mul 4),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]

theorem perronDifferenceEnergy_le_scaled_low
    (F : ℝ → ℂ) (hF : Continuous F) {X H₁ H₂ : ℕ}
    (hH₁ : 0 < H₁) (hH₂ : 0 < H₂) (hH₁X : H₁ ≤ X) (hH₂X : H₂ ≤ X)
    {A B : ℝ} (hAB : A ≤ B) :
    perronDifferenceEnergy X F H₁ H₂ A B ≤
      4 * lemma14UniversalScaledLowConstant * ((X : ℝ) + 1) *
        ∫ t in A..B, Complex.normSq (F t) := by
  let P : ℝ := X + 1
  let Q : ℝ := (2 * X : ℕ) + 1
  have hPQ : P ≤ Q := by dsimp [P, Q]; exact_mod_cast (show X + 1 ≤ 2 * X + 1 by omega)
  have h₁ : (0 : ℝ) < H₁ := by exact_mod_cast hH₁
  have h₂ : (0 : ℝ) < H₂ := by exact_mod_cast hH₂
  have hc₁ := perronSegment_continuousOn_window F hF X h₁ A B
  have hc₂ := perronSegment_continuousOn_window F hF X h₂ A B
  have hi₁ := (Complex.continuous_normSq.comp_continuousOn hc₁).intervalIntegrable (μ := volume)
  have hi₂ := (Complex.continuous_normSq.comp_continuousOn hc₂).intervalIntegrable (μ := volume)
  have hid := (Complex.continuous_normSq.comp_continuousOn (hc₁.sub hc₂)).intervalIntegrable (μ := volume)
  have hm := intervalIntegral.integral_mono_on hPQ hid
    ((hi₁.add hi₂).const_mul 2) (fun x _ => normSq_sub_le_two_mul_add _ _)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi₁ hi₂] at hm
  have hb₁ := integral_normSq_perronKernelSegmentOn_le_shifted_scaled_low F hF hH₁ hH₁X hAB
  have hb₂ := integral_normSq_perronKernelSegmentOn_le_shifted_scaled_low F hF hH₂ hH₂X hAB
  change perronDifferenceEnergy X F H₁ H₂ A B ≤ _ at hm
  simp only [Function.comp_def] at hm
  linarith

/-- Finite reduction with an explicit proof draft, retaining the middle energy. -/
theorem dyadic_twoLength_threeBand
    (S : Finset ℕ) {f : ℕ → ℂ} (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {Y X H₁ H₂ : ℕ} (hY : 0 < Y) (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    (hH₁X : H₁ ≤ X) (hH₂X : H₂ ≤ X) {T U : ℝ}
    (hT : 0 ≤ T) (hU : 0 < U) (hTU : T ≤ U) :
    dyadicTwoLengthShortMeanSquareAt S f Y X H₁ H₂ ≤
      4 * ((X : ℝ) *
        (‖(((2 * Real.pi : ℝ) : ℂ))⁻¹‖ *
          (2 * T ^ 2 * ((H₁ : ℝ) + H₂) / ((X : ℝ) + 1))) ^ 2) +
      32 * lemma14UniversalScaledLowConstant * ((X : ℝ) + 1) *
        ((∫ t in -U..-T, Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t)) +
          ∫ t in T..U, Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t)) +
      8 * (lemma14UniversalPerronSegmentSafeWeightedCoefficient
          ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H₁ +
        lemma14UniversalPerronSegmentSafeWeightedCoefficient
          ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H₂) *
        (16 / ((Y : ℝ) * U) + 16 * Real.pi / U ^ 2) := by
  let F := dyadicVerticalDirichletPolynomial S f Y
  have hF : Continuous F := continuous_dyadicVerticalDirichletPolynomial S f Y
  have hbase := dyadicTwoLengthShortMeanSquare_le_central_add_weightedHigh_continuous
    S f Y (X := X) hH₁ hH₂ hU (by positivity : 0 ≤ 16 / ((Y : ℝ) * U) + 16 * Real.pi / U ^ 2)
    (fun V hUV => lemma14TwoSidedWeightedTail_dyadic_le_mean S hf hY hU hUV)
  have hsplit := perronDifferenceEnergy_split_le F hF X
    (H₁ := (H₁ : ℝ)) (H₂ := (H₂ : ℝ))
    (by exact_mod_cast hH₁) (by exact_mod_cast hH₂) T U
  have hcentral := integral_normSq_dyadicTwoLengthPerronCentral_le S hf Y (X := X) hH₁ hH₂ hT
  have hnegative := perronDifferenceEnergy_le_scaled_low F hF hH₁ hH₂ hH₁X hH₂X
    (show -U ≤ -T by linarith)
  have hpositive := perronDifferenceEnergy_le_scaled_low F hF hH₁ hH₂ hH₁X hH₂X hTU
  change dyadicTwoLengthShortMeanSquareAt S f Y X H₁ H₂ ≤
    2 * perronDifferenceEnergy X F H₁ H₂ (-U) U + _ at hbase
  change perronDifferenceEnergy X F H₁ H₂ (-T) T ≤ _ at hcentral
  dsimp only [F] at hnegative hpositive
  nlinarith

end

end JSP1006
