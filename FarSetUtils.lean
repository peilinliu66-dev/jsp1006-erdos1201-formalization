/- Measurable frequency restrictions. UNCOMPILED DRAFT. -/
import FarCofactors
import ErdosProblems.Erdos67b.MRSelectedNoSmallEnergy

open scoped Classical

open MeasureTheory
open scoped Interval
open Erdos67b

namespace JSP1006

def farFrequencySet (X : ℕ) : Set ℝ :=
  {t | 1 + Real.log (X : ℝ) ^ 2 ≤ |t|}

theorem measurableSet_farFrequencySet (X : ℕ) : MeasurableSet (farFrequencySet X) :=
  measurableSet_le measurable_const continuous_abs.measurable

def farNoSmallFrequencySet (eta p q : ℝ) (f : ℕ → ℂ) (J X : ℕ) : Set ℝ :=
  mrNoSmallFrequencyClass (mrArithmeticSmallFrequencySet eta p q f) J ∩ farFrequencySet X

theorem measurableSet_farNoSmallFrequencySet (eta p q : ℝ) (f : ℕ → ℂ) (J X : ℕ) :
    MeasurableSet (farNoSmallFrequencySet eta p q f J X) :=
  (measurableSet_mrArithmeticNoSmall eta p q f J).inter (measurableSet_farFrequencySet X)

/-- Restricting a nonnegative frequency integrand can only decrease its integral. -/
theorem integral_indicator_mono_set {A B : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B)
    {g : ℝ → ℝ} (hg : Continuous g) (hnonneg : ∀ t, 0 ≤ g t)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, A.indicator g t) ≤ ∫ t in -T..T, B.indicator g t := by
  have hi (E : Set ℝ) (hE : MeasurableSet E) :
      IntervalIntegrable (E.indicator g) volume (-T) T := by
    rw [intervalIntegrable_iff]
    exact (intervalIntegrable_iff.mp (hg.intervalIntegrable (-T) T)).indicator hE
  apply intervalIntegral.integral_mono_on (by linarith) (hi A hA) (hi B hB)
  intro t _
  by_cases ht : t ∈ A
  · simpa only [Set.indicator_of_mem ht, Set.indicator_of_mem (hAB ht)] using le_refl (g t)
  · rw [Set.indicator_of_notMem ht]
    exact Set.indicator_nonneg (fun x _ => hnonneg x) t

end JSP1006
