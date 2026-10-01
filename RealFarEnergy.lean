/-
Unconditional real far-frequency energy and typicality input.
UNCOMPILED DRAFT. This is a bridge component, not the final JSP1006 theorem.
-/
import FarScheduledEnergy

open scoped Classical

open Filter MeasureTheory
open scoped BigOperators ComplexConjugate Interval
open Erdos67b

namespace JSP1006

noncomputable section

theorem real_far_typical_energy_and_density
    {epsilon delta : ℝ} (hepsilon : 0 < epsilon) (hdelta : 0 < delta) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ ∃ X₀ : ℕ, 2 ≤ X₀ ∧
      ∀ X : ℕ, X₀ ≤ X → ∃ blocks : Finset (ℕ × ℕ),
        (∀ Z : ℕ, Z ≤ 3 * X →
          ((atypicalFactorizationSet blocks Z).card : ℝ) ≤ delta * X) ∧
        ∀ f : ℕ → ℂ, IsMultiplicativeOnPositiveNat f →
          (∀ n, 0 < n → conj (f n) = f n) →
          (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        ∀ T : ℝ, 0 ≤ T → T ≤ c * X →
          (∫ t in -T..T, (farFrequencySet X).indicator
            (fun t => ‖mrTypicalDyadicPolynomial blocks f X t‖ ^ 2) t) ≤ epsilon := by
  obtain ⟨p, q, _hQ, _hq, _hp, _hpq, _hlq, _hbudget, _hmertens,
      M₀, Y₀, _hM₀, hY₀, henergy⟩ :=
    exists_far_scheduled_small_energy_and_density
      (by norm_num : (0 : ℝ) < 1 / 12) (le_refl (1 / 12 : ℝ))
      hepsilon hdelta 0
  obtain ⟨Z₀, hfar⟩ := eventually_atTop.mp (eventually_farNonpretentious M₀)
  refine ⟨Real.exp (-q), Real.exp_pos _, mrExp_neg_initial_le_half _hq, max Y₀ Z₀,
    hY₀.trans (le_max_left _ _), ?_⟩
  intro X hX
  have hXY : Y₀ ≤ X := (le_max_left _ _).trans hX
  have hXZ : Z₀ ≤ X := (le_max_right _ _).trans hX
  obtain ⟨J, _hJ, _hupper, _hnext, hdensity, hmain⟩ :=
    henergy (M := M₀) le_rfl hXY
  refine ⟨mrScheduledBlocks p q J, hdensity, ?_⟩
  intro f hmul hreal hbound T hT hTX
  have hfarX : FarNonpretentious f M₀ X := hfar X hXZ f hreal hbound
  apply hmain hmul hbound hfarX hT
  simpa only [mul_comm] using hTX

end

end JSP1006

#print axioms JSP1006.real_far_typical_energy_and_density
