/- Frequency recombination after a measurable restriction. UNCOMPILED DRAFT. -/
import FarSetUtils
import ErdosProblems.Erdos67b.MRClassSummation

open scoped Classical

open Filter MeasureTheory
open scoped BigOperators Interval
open Erdos67b

namespace JSP1006

theorem indicator_nested_eq {α : Type*} (A B : Set α) (g : α → ℝ) :
    A.indicator (B.indicator g) = (A ∩ B).indicator g := by
  classical
  funext x
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [ha, hb]

theorem far_typical_energy_le_firstSmall_add_noSmall
    (J : ℕ) (hJ : 1 ≤ J) {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hqexp : Real.exp 1 ≤ q₁) (hpq : p₁ ≤ q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 0 < X) (hscale : Real.exp q₁ ≤ X) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, (farFrequencySet X).indicator
      (fun t => ‖mrTypicalDyadicPolynomial (mrScheduledBlocks p₁ q₁ J) f X t‖ ^ 2) t) ≤
      mrFirstSmallEnergyBudget eta p₁ q₁ X J T +
        ∫ t in -T..T, (farNoSmallFrequencySet eta p₁ q₁ f J X).indicator
          (fun t => ‖mrTypicalDyadicPolynomial (mrScheduledBlocks p₁ q₁ J) f X t‖ ^ 2) t := by
  let g : ℝ → ℝ := fun t => ‖mrTypicalDyadicPolynomial (mrScheduledBlocks p₁ q₁ J) f X t‖ ^ 2
  let small := mrArithmeticSmallFrequencySet eta p₁ q₁ f
  let F := farFrequencySet X
  have hg : Continuous g := (continuous_logarithmicDirichletPolynomial _ _).norm.pow 2
  have hF : MeasurableSet F := measurableSet_farFrequencySet X
  have hsmall (j : ℕ) : MeasurableSet (small j) :=
    measurableSet_mrScheduledSmallFrequencySet _ _ _ _ _ j
  have hint : IntervalIntegrable (F.indicator g) volume (-T) T := by
    rw [intervalIntegrable_iff]
    exact (intervalIntegrable_iff.mp (hg.intervalIntegrable (-T) T)).indicator hF
  have hpart := intervalIntegral_eq_firstSmall_add_noSmall hsmall J hint
  have hindex : Finset.range (J + 1) = insert 0 (Finset.Icc 1 J) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hzero : (∫ t in -T..T, (disjointed small 0).indicator (F.indicator g) t) = 0 := by
    change (∫ t in -T..T,
      (disjointed (mrArithmeticSmallFrequencySet eta p₁ q₁ f) 0).indicator (F.indicator g) t) = 0
    rw [mrArithmetic_firstSmall_zero]
    simp
  rw [hindex, Finset.sum_insert (by simp), hzero, zero_add] at hpart
  simp_rw [indicator_nested_eq] at hpart
  have hfirst :
      (∑ j ∈ Finset.Icc 1 J, ∫ t in -T..T, (disjointed small j ∩ F).indicator g t) ≤
        ∑ j ∈ Finset.Icc 1 J, ∫ t in -T..T, (disjointed small j).indicator g t := by
    apply Finset.sum_le_sum
    intro j _
    exact integral_indicator_mono_set ((MeasurableSet.disjointed hsmall j).inter hF)
      (MeasurableSet.disjointed hsmall j) Set.inter_subset_left hg (fun t => sq_nonneg _) hT
  have hpaid := mrAllFirstSmall_energy_le J hJ heta0 heta1 hp hqexp hpq hbudget
    hmul hbound hX hscale hT
  change (∫ t in -T..T, F.indicator g t) ≤ mrFirstSmallEnergyBudget eta p₁ q₁ X J T +
    ∫ t in -T..T, (mrNoSmallFrequencyClass small J ∩ F).indicator g t
  rw [hpart]
  exact add_le_add (hfirst.trans hpaid) le_rfl

end JSP1006
