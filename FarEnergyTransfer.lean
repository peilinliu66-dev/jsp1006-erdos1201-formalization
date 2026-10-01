/- Matching the exact MR cutoff to the Perron middle band. UNCOMPILED DRAFT. -/
import RealFarEnergy
import PerronThreeBand
import ErdosProblems.Erdos67b.MRTypicalShortBoundary

open scoped Classical

open MeasureTheory
open scoped Interval
open Erdos67b

namespace JSP1006
noncomputable section

theorem farFrequencySet_neg_iff (X : ℕ) (t : ℝ) :
    -t ∈ farFrequencySet X ↔ t ∈ farFrequencySet X := by
  simp [farFrequencySet]

theorem integral_far_dyadic_typical_eq
    (blocks : Finset (ℕ × ℕ)) (f : ℕ → ℂ) {X Z : ℕ} (hZ : 2 * X ≤ Z) (U : ℝ) :
    (∫ t in -U..U, (farFrequencySet X).indicator
      (fun t => Complex.normSq (dyadicVerticalDirichletPolynomial
        (typicalFactorizationSet blocks Z) f X t)) t) =
    ∫ t in -U..U, (farFrequencySet X).indicator
      (fun t => ‖mrTypicalDyadicPolynomial blocks f X t‖ ^ 2) t := by
  have heq (t : ℝ) : (farFrequencySet X).indicator
      (fun t => Complex.normSq (dyadicVerticalDirichletPolynomial
        (typicalFactorizationSet blocks Z) f X t)) t =
      (farFrequencySet X).indicator
        (fun t => ‖mrTypicalDyadicPolynomial blocks f X t‖ ^ 2) (-t) := by
    by_cases ht : t ∈ farFrequencySet X
    · rw [Set.indicator_of_mem ht,
        Set.indicator_of_mem ((farFrequencySet_neg_iff X t).mpr ht),
        dyadicVerticalDirichletPolynomial_typical_eq blocks f hZ,
        Complex.normSq_eq_norm_sq]
    · rw [Set.indicator_of_notMem ht,
        Set.indicator_of_notMem (by simpa only [farFrequencySet_neg_iff] using ht)]
  simp_rw [heq]
  simpa only [neg_neg] using intervalIntegral.integral_comp_neg
    ((farFrequencySet X).indicator (fun t => ‖mrTypicalDyadicPolynomial blocks f X t‖ ^ 2))
    (a := -U) (b := U)

/-- Keeping the two bands separately costs at most a harmless factor two. -/
theorem middle_energy_le_twice_far {X : ℕ} {F : ℝ → ℂ} (hF : Continuous F)
    {U E : ℝ} (hU : 0 ≤ U) (hTU : 1 + Real.log (X : ℝ) ^ 2 ≤ U)
    (hfar : (∫ t in -U..U, (farFrequencySet X).indicator
      (fun t => Complex.normSq (F t)) t) ≤ E) :
    (∫ t in -U..-(1 + Real.log (X : ℝ) ^ 2), Complex.normSq (F t)) +
      (∫ t in (1 + Real.log (X : ℝ) ^ 2)..U, Complex.normSq (F t)) ≤ 2 * E := by
  let T := 1 + Real.log (X : ℝ) ^ 2
  let g := (farFrequencySet X).indicator (fun t => Complex.normSq (F t))
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hi : IntervalIntegrable g volume (-U) U := by
    rw [intervalIntegrable_iff]
    exact (intervalIntegrable_iff.mp
      ((Complex.continuous_normSq.comp hF).intervalIntegrable (-U) U)).indicator
        (measurableSet_farFrequencySet X)
  have hg : ∀ t, 0 ≤ g t := Set.indicator_nonneg (fun t _ => Complex.normSq_nonneg _)
  have hleft : (∫ t in -U..-T, Complex.normSq (F t)) = ∫ t in -U..-T, g t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ≤ -T := (Set.uIcc_of_le (by linarith : -U ≤ -T) ▸ ht).2
    have hmem : t ∈ farFrequencySet X := by
      change T ≤ |t|
      rw [abs_of_nonpos (by linarith)]
      linarith
    exact (Set.indicator_of_mem hmem (fun u : ℝ => Complex.normSq (F u))).symm
  have hright : (∫ t in T..U, Complex.normSq (F t)) = ∫ t in T..U, g t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : T ≤ t := (Set.uIcc_of_le hTU ▸ ht).1
    have hmem : t ∈ farFrequencySet X := by
      change T ≤ |t|
      rw [abs_of_nonneg (by linarith)]
      exact ht'
    exact (Set.indicator_of_mem hmem (fun u : ℝ => Complex.normSq (F u))).symm
  have hl : (∫ t in -U..-T, g t) ≤ ∫ t in -U..U, g t :=
    intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
      (Filter.Eventually.of_forall hg) hi
  have hr : (∫ t in T..U, g t) ≤ ∫ t in -U..U, g t :=
    intervalIntegral.integral_mono_interval (by linarith) hTU le_rfl
      (Filter.Eventually.of_forall hg) hi
  rw [hleft, hright]
  change (∫ t in -U..U, g t) ≤ E at hfar
  linarith

end
end JSP1006
