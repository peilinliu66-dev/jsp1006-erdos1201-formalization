/-
Draft bridge lemma for the real-valued MR branch. UNCOMPILED.
Imports refer to the pinned plby source tree recorded in SOURCE_MANIFEST.json.
No unproved hypothesis is introduced: the imported little-oh L-series estimate
is an existing theorem, not a field supplied by this project.
-/
import ErdosProblems.Erdos67b.MRRealTwistSeparationQuantitative

open scoped Classical

open Filter
open scoped ComplexConjugate LSeries.notation
open Erdos67b

namespace JSP1006

noncomputable section

/-- Real one-bounded coefficients are uniformly far from all twists with
1 <= |t| <= X, once X is large. The omitted neighbourhood of zero is essential. -/
theorem eventually_real_far_twist_distance (A : ℝ) :
    ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, 0 < n → ‖f n‖ ≤ 1) →
      ∀ t : ℝ, 1 ≤ |t| → |t| ≤ (X : ℝ) →
        A ≤ pretentiousDistSq f (archimedeanTwist t) X := by
  let C : ℝ := 4 * A + oppositeTwistEulerLoss + Real.log 2
  let eta : ℝ := Real.exp (-C)
  have heta : 0 < eta := Real.exp_pos _
  obtain ⟨V₀, hV₀, hL⟩ :=
    LSeriesSublinear.boundedConductorLSeriesSublinear 1 eta heta
  let V : ℝ := max 2 (V₀ : ℝ)
  obtain ⟨K, hK, hcompact⟩ :=
    exists_uniform_norm_riemannZeta_compact_two V (le_max_left _ _)
  have hlogTop : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ X : ℕ in atTop,
      max 1 (K / (2 * eta)) ≤ Real.log (X : ℝ) :=
    hlogTop.eventually (eventually_ge_atTop _)
  filter_upwards [hlarge, eventually_ge_atTop 4] with X hlogLarge hX
  intro f hreal hbound t htLower htUpper
  let u : ℝ := Real.log (X : ℝ)
  let v : ℝ := -2 * t
  let sigma : ℝ := 1 + u⁻¹
  have huOne : 1 ≤ u := (le_max_left _ _).trans hlogLarge
  have hu : 0 < u := lt_of_lt_of_le zero_lt_one huOne
  have hsigma1 : 1 < sigma := by
    dsimp only [sigma]
    linarith [inv_pos.mpr hu]
  have hsigma2 : sigma ≤ 2 := by
    dsimp only [sigma]
    have hi : u⁻¹ ≤ 1 := (inv_le_one₀ hu).mpr huOne
    linarith
  have hvabs : |v| = 2 * |t| := by
    dsimp only [v]
    rw [abs_mul]
    norm_num
  have hvTwo : 2 ≤ |v| := by rw [hvabs]; linarith
  have hvUpper : |v| ≤ 2 * (X : ℝ) := by rw [hvabs]; linarith
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hpoint : (sigma : ℂ) + Complex.I * (v : ℂ) =
      polynomialHeightEulerPoint X v := rfl
  have hpointRe : (polynomialHeightEulerPoint X v).re = sigma := by
    rw [← hpoint]
    simp
  have hzetaNe : riemannZeta (polynomialHeightEulerPoint X v) ≠ 0 := by
    rw [← LSeries_dirichletCharacter_one_eq_riemannZeta (by
      rw [hpointRe]
      exact hsigma1)]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re
      (1 : DirichletCharacter ℂ 1) (by rw [hpointRe]; exact hsigma1)
  have hnorm : ‖riemannZeta (polynomialHeightEulerPoint X v)‖ ≤ 2 * eta * u := by
    by_cases hvHigh : (V₀ : ℝ) ≤ |v|
    · have hLnorm : ‖riemannZeta (polynomialHeightEulerPoint X v)‖ ≤
          eta * Real.log |v| := by
        rw [← hpoint,
          ← LSeries_dirichletCharacter_one_eq_riemannZeta (by
            simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
              Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im,
              mul_zero, sub_zero, add_zero]
            exact hsigma1)]
        exact hL 1 (by norm_num) (by norm_num)
          (1 : DirichletCharacter ℂ 1) sigma v hvHigh hsigma1 hsigma2
      have hlogV : Real.log |v| ≤ 2 * u := by
        have h₁ := Real.log_le_log (by linarith : 0 < |v|) hvUpper
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hXpos.ne'] at h₁
        have h₂ : Real.log 2 ≤ u := Real.log_le_log (by norm_num)
          (by exact_mod_cast (show 2 ≤ X by omega))
        dsimp only [u] at *
        linarith
      exact hLnorm.trans (by nlinarith [mul_le_mul_of_nonneg_left hlogV heta.le])
    · have hvV : |v| ≤ V := (le_of_not_ge hvHigh).trans (le_max_right _ _)
      have hKbound : K ≤ 2 * eta * u := by
        have hku : K / (2 * eta) ≤ u := (le_max_right _ _).trans hlogLarge
        have hmul := (div_le_iff₀ (by positivity : 0 < 2 * eta)).mp hku
        nlinarith
      exact (hcompact sigma v hsigma1.le hsigma2 hvTwo hvV).trans hKbound
  have hlogNorm : Real.log ‖riemannZeta (polynomialHeightEulerPoint X v)‖ ≤
      Real.log u - 4 * A - oppositeTwistEulerLoss := by
    have h := Real.log_le_log (norm_pos_iff.mpr hzetaNe) hnorm
    rw [Real.log_mul (mul_pos (by norm_num) heta).ne' hu.ne',
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) heta.ne'] at h
    have hetaLog : Real.log eta = -C := by dsimp only [eta]; rw [Real.log_exp]
    rw [hetaLog] at h
    dsimp only [C] at h
    linarith
  have hdist :=
    one_fourth_log_log_sub_log_norm_riemannZeta_sub_loss_le_realDistSq
      hreal hbound hX t
  change (Real.log u - Real.log ‖riemannZeta (polynomialHeightEulerPoint X v)‖ -
      oppositeTwistEulerLoss) / 4 ≤ pretentiousDistSq f (archimedeanTwist t) X at hdist
  linarith

end

end JSP1006
