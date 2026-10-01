/- Strong prime-counting input for logarithmically short intervals. UNCOMPILED DRAFT. -/
import Mathlib
import BoundedGaps.PrimeNumberTheorem.Analytic.StrongChebyshev

open scoped Classical

open Filter Asymptotics
open scoped Topology Asymptotics

namespace JSP1006

theorem log_pow_exp_neg_sqrtLog_tendsto (B : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ B *
      Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => Real.sqrt (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((2 * B : ℕ) : ℝ) c hc).comp ht
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Function.comp_apply, Real.rpow_natCast]
  rw [pow_mul, Real.sq_sqrt (Real.log_nonneg (by exact_mod_cast hn))]

theorem log_pow_div_sqrt_tendsto (B : ℕ) :
    Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ B / Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (B : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, Real.rpow_natCast, ← Real.sqrt_eq_rpow] using h

/-- Any prescribed inverse-logarithmic relative error is available at all large
natural endpoints. Prime powers are removed with Mathlib's O(sqrt x) estimate. -/
theorem theta_error_eventually_le_log_power (B : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      |Chebyshev.theta (n : ℝ) - (n : ℝ)| ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ B := by
  obtain ⟨C, c, hC, hc, N₀, _hN₀, hpsi⟩ :=
    BoundedGaps.PrimeNumberTheorem.exists_abs_chebyshevPsi_sub_natCast_le_exp_neg_sqrtLog
  have hbig :
      (fun n : ℕ => Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ)) =O[atTop]
        (fun n : ℕ => Real.sqrt (n : ℝ)) := by
    simpa only [Function.comp_def, Pi.sub_apply] using
      Chebyshev.isBigO_psi_sub_theta_sqrt.comp_tendsto tendsto_natCast_atTop_atTop
  obtain ⟨K, hK, hprimePowers⟩ := (Asymptotics.isBigO_iff').mp hbig
  have hdecay₁ : Tendsto
      (fun n : ℕ => C * ((Real.log (n : ℝ)) ^ B *
        Real.exp (-c * Real.sqrt (Real.log (n : ℝ))))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (log_pow_exp_neg_sqrtLog_tendsto B hc).const_mul C
  have hdecay₂ : Tendsto
      (fun n : ℕ => K * ((Real.log (n : ℝ)) ^ B / Real.sqrt (n : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (log_pow_div_sqrt_tendsto B).const_mul K
  filter_upwards [eventually_ge_atTop (max N₀ 2), hprimePowers,
    hdecay₁.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hdecay₂.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
    with n hn hpp hsmall₁ hsmall₂
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : 2 ≤ n := (le_max_right _ _).trans hn
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnPos
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogPow : 0 < (Real.log (n : ℝ)) ^ B := pow_pos hlog B
  have hpsi' := hpsi n hn₀
  have hpp' : |Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ)| ≤
      K * Real.sqrt (n : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hpp
  have habs : |Chebyshev.theta (n : ℝ) - (n : ℝ)| ≤
      C * ((n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))) +
        K * Real.sqrt (n : ℝ) := by
    have heq : Chebyshev.theta (n : ℝ) - (n : ℝ) =
        (Chebyshev.psi (n : ℝ) - (n : ℝ)) -
        (Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ)) := by ring
    rw [heq]
    exact (abs_sub _ _).trans (add_le_add hpsi' hpp')
  have hfirst := mul_le_mul_of_nonneg_right hsmall₁.le hnPos.le
  have hsmall₂' : (K * (Real.log (n : ℝ)) ^ B) / Real.sqrt (n : ℝ) ≤ 1 / 2 := by
    simpa only [mul_div_assoc] using hsmall₂.le
  have hsecond := mul_le_mul_of_nonneg_right
    ((div_le_iff₀ hsqrt).mp hsmall₂') hsqrt.le
  have hsquare : (Real.sqrt (n : ℝ)) ^ 2 = n := Real.sq_sqrt hnPos.le
  apply (le_div_iff₀ hlogPow).mpr
  have hbound := mul_le_mul_of_nonneg_right habs hlogPow.le
  nlinarith

end JSP1006
