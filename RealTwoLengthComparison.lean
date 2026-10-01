/- A genuine real-valued two-length theorem, with all MR inputs discharged.
   UNCOMPILED DRAFT: elaboration and kernel checking remain to be performed. -/
import ComparisonBudget

open scoped Classical

open Filter MeasureTheory
open scoped BigOperators ComplexConjugate Interval Topology
open Erdos67b

namespace JSP1006
noncomputable section

theorem comparisonVanishingCost_tendsto :
    Tendsto comparisonVanishingCost atTop (𝓝 0) := by
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun X : ℕ => (Real.log (X : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have h₁ := (hinv.pow 24).const_mul (2048 * ‖(((2 * Real.pi : ℝ) : ℂ))⁻¹‖ ^ 2)
  have h₂ := (hinv.pow 16).const_mul 16
  change Tendsto (fun X : ℕ => comparisonVanishingCost X) atTop (𝓝 0)
  simpa [comparisonVanishingCost, div_eq_mul_inv, inv_pow] using h₁.add h₂

theorem eventually_far_cutoff {c : ℝ} (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop, 1 + Real.log (X : ℝ) ^ 2 ≤ c * X := by
  have hinv : Tendsto (fun X : ℕ => (X : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ) ^ 2 / (X : ℝ)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, Real.rpow_natCast] using h
  have hs := hinv.add hlog
  simp only [zero_add] at hs
  filter_upwards [eventually_ge_atTop 1, hs.eventually (gt_mem_nhds hc)] with X hX hsmall
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have heq : (X : ℝ)⁻¹ + Real.log (X : ℝ) ^ 2 / (X : ℝ) =
      (1 + Real.log (X : ℝ) ^ 2) / (X : ℝ) := by simp only [add_div, one_div]
  rw [heq] at hsmall
  exact ((div_lt_iff₀ hXR).mp hsmall).le

/-- The comparison is uniform over the function, including a cutoff depending on X.
The short length is fixed before the ambient scale tends to infinity. -/
theorem real_twoLength_comparison {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ H₀ : ℕ, 0 < H₀ ∧ ∀ H : ℕ, H₀ ≤ H →
      ∀ᶠ X : ℕ in atTop,
        0 < longLength X ∧ H ≤ longLength X ∧ longLength X ≤ X ∧
        ∀ f : ℕ → ℂ, IsMultiplicativeOnPositiveNat f →
          (∀ n, 0 < n → conj (f n) = f n) →
          (∀ n, 0 < n → ‖f n‖ ≤ 1) →
          twoLengthEnergy f X H (longLength X) ≤ zeta * X := by
  let epsilon := zeta / (1024 * (lemma14UniversalScaledLowConstant + 1))
  let delta := zeta / 64
  have hlow := lemma14UniversalScaledLowConstant_nonneg
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨c, hc, _hcHalf, X₀, _hX₀, htypical⟩ :=
    real_far_typical_energy_and_density hepsilon hdelta
  have htailLimit : Tendsto (fun H : ℕ => comparisonTailCost c / (H : ℝ) ^ 2) atTop (𝓝 0) := by
    have hi : Tendsto (fun H : ℕ => (H : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa [div_eq_mul_inv, inv_pow] using (hi.pow 2).const_mul (comparisonTailCost c)
  obtain ⟨H₁, htail⟩ := eventually_atTop.mp
    (htailLimit.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < zeta / 4)))
  refine ⟨max 1 H₁, by omega, ?_⟩
  intro H hH
  have hHpos : 0 < H := by omega
  have htailSmall := (htail H (by omega)).le
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop X₀, eventually_ge_atTop (H ^ 2),
    eventually_longLength_properties, eventually_far_cutoff hc,
    hlog.eventually (eventually_ge_atTop 1),
    comparisonVanishingCost_tendsto.eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < zeta / 4))]
    with X hX₀ hHX hlength hcut hlogX hsmall
  obtain ⟨hX3, hL, hLX, _hscale, _hlogPower, hcofactor⟩ := hlength
  have hHL : H ≤ longLength X := by have h := hcofactor H hHX; omega
  refine ⟨hL, hHL, hLX, ?_⟩
  intro f hmul hreal hbound
  obtain ⟨blocks, hdensity, henergy⟩ := htypical X hX₀
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hfull := twoLengthEnergy_le_explicit_budget blocks hbound hHpos hHL hLX hlogX hc
    hepsilon.le hdelta.le hcut (hdensity (3 * X) le_rfl)
    (henergy f hmul hreal hbound (c * X) (mul_pos hc hXpos).le le_rfl)
  have hepsilonSmall : 256 * lemma14UniversalScaledLowConstant * epsilon ≤ zeta / 4 := by
    dsimp [epsilon]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    have hden : 0 < 1024 * (lemma14UniversalScaledLowConstant + 1) := by positivity
    have hratio : lemma14UniversalScaledLowConstant / (lemma14UniversalScaledLowConstant + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith)
    calc
      256 * lemma14UniversalScaledLowConstant *
          (zeta / (1024 * (lemma14UniversalScaledLowConstant + 1))) * 4 =
          zeta * (lemma14UniversalScaledLowConstant / (lemma14UniversalScaledLowConstant + 1)) := by
            field_simp; ring
      _ ≤ zeta * 1 := mul_le_mul_of_nonneg_left hratio hzeta.le
      _ = zeta := mul_one _
  have hdeltaSmall : 16 * delta = zeta / 4 := by dsimp [delta]; ring
  have hbudget : comparisonVanishingCost X + 256 * lemma14UniversalScaledLowConstant * epsilon +
      16 * delta + comparisonTailCost c / (H : ℝ) ^ 2 ≤ zeta := by linarith
  exact hfull.trans (mul_le_mul_of_nonneg_right hbudget hXpos.le)

end
end JSP1006

#print axioms JSP1006.real_twoLength_comparison
