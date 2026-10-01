/- Uniform long-window deficit: finite arithmetic and counting. UNCOMPILED DRAFT. -/
import CofactorCounting

open scoped Classical

open scoped BigOperators

namespace JSP1006

theorem theta_endpoint_error_transfer {X H q a : ℕ}
    (hq : 0 < q) (ha : 2 ≤ a) (hqa : q * a ≤ 3 * X)
    (hlog : Real.log (X : ℝ) ≤ 2 * Real.log (a : ℝ))
    (hlogX : 0 < Real.log (X : ℝ))
    (hlength : (X : ℝ) ≤ 2 * H * Real.log (X : ℝ) ^ 16)
    (hlarge : 48 * (2 : ℝ) ^ 40 ≤ Real.log (X : ℝ) ^ 24)
    (htheta : |Chebyshev.theta (a : ℝ) - (a : ℝ)| ≤
      (a : ℝ) / Real.log (a : ℝ) ^ 40) :
    |Chebyshev.theta (a : ℝ) - (a : ℝ)| ≤ (H : ℝ) / (8 * q) := by
  have hqaR : (q : ℝ) * a ≤ 3 * X := by exact_mod_cast hqa
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hloga : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hpow : Real.log (X : ℝ) ^ 40 ≤ (2 : ℝ) ^ 40 * Real.log (a : ℝ) ^ 40 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hlogX.le hlog 40
  have hlength' := mul_le_mul_of_nonneg_right hlength (pow_nonneg hlogX.le 24)
  have hpowers : Real.log (X : ℝ) ^ 16 * Real.log (X : ℝ) ^ 24 =
      Real.log (X : ℝ) ^ 40 := by rw [← pow_add]
  have hlength'' : (X : ℝ) * Real.log (X : ℝ) ^ 24 ≤
      2 * H * Real.log (X : ℝ) ^ 40 := by
    simpa only [mul_assoc, hpowers] using hlength'
  have hlarge' := mul_le_mul_of_nonneg_left hlarge (Nat.cast_nonneg X)
  have hpow' := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg H)
  have hmass : (24 : ℝ) * X ≤ (H : ℝ) * Real.log (a : ℝ) ^ 40 := by
    norm_num at hlarge' hpow'
    nlinarith
  apply htheta.trans
  apply (div_le_div_iff₀ (pow_pos hloga 40) (by positivity : (0 : ℝ) < 8 * q)).mpr
  nlinarith

theorem log_le_reciprocal_sum (R : ℕ) :
    Real.log (R : ℝ) ≤ ∑ q ∈ Finset.Icc 1 R, (1 : ℝ) / q := by
  have h := log_le_harmonic_floor (R : ℝ) (Nat.cast_nonneg R)
  simpa only [Nat.floor_natCast, harmonic_eq_sum_Icc, Rat.cast_sum,
    Rat.cast_inv, Rat.cast_natCast, one_div] using h

/-- Every starting point in the ambient dyadic window has the same positive
deficit. The hypotheses are elementary scale conditions plus a proved theta bound. -/
theorem smooth_long_average_deficit {m R X n H : ℕ}
    (hm : 3 ≤ m) (hR : 2 ≤ R) (hX : 3 ≤ X)
    (hscale : R ^ m ≤ X) (hnLower : X ≤ n) (hnUpper : n ≤ 2 * X)
    (hHX : H ≤ X) (hHR : 8 * R ≤ H)
    (hsquare : 3 * X ≤ (R ^ (m - 1)) * (R ^ (m - 1)))
    (hlogScale : Real.log (X : ℝ) ≤ ((m : ℝ) + 1) * Real.log (R : ℝ))
    (hlength : (X : ℝ) ≤ 2 * H * Real.log (X : ℝ) ^ 16)
    (hlarge : 48 * (2 : ℝ) ^ 40 ≤ Real.log (X : ℝ) ^ 24)
    (htheta : ∀ a : ℕ, R ≤ a →
      |Chebyshev.theta (a : ℝ) - (a : ℝ)| ≤ (a : ℝ) / Real.log (a : ℝ) ^ 40) :
    (∑ j ∈ Finset.Icc 1 H, smoothIndicator (R ^ (m - 1)) (n + j)) / H ≤
          1 - 1 / (4 * ((m : ℝ) + 1)) := by
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogR : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hpowEq : R * R ^ (m - 1) = R ^ m := by
    rw [Nat.mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
  have hRpow : R ≤ R ^ (m - 1) := by
    calc
      R = R ^ 1 := by simp
      _ ≤ R ^ (m - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hRy : R * R ^ (m - 1) ≤ n := by rw [hpowEq]; exact hscale.trans hnLower
  have htop : n + H ≤ R ^ (m - 1) * R ^ (m - 1) := (by omega : n + H ≤ 3 * X).trans hsquare
  have hcounts (q : ℕ) (hq : q ∈ Finset.Icc 1 R) :
      (H : ℝ) / (4 * q * Real.log (X : ℝ)) ≤
        ((primeInterval (n / q) ((n + H) / q)).card : ℝ) := by
    obtain ⟨hq1, hqR⟩ := Finset.mem_Icc.mp hq
    have haLower : R ^ (m - 1) ≤ n / q := by
      apply (Nat.le_div_iff_mul_le hq1).mpr
      calc
        R ^ (m - 1) * q ≤ R ^ (m - 1) * R := Nat.mul_le_mul_left _ hqR
        _ = R * R ^ (m - 1) := Nat.mul_comm _ _
        _ ≤ n := hRy
    have hab : n / q ≤ (n + H) / q := Nat.div_le_div_right (Nat.le_add_right n H)
    have haR : R ≤ n / q := hRpow.trans haLower
    have hbR : R ≤ (n + H) / q := haR.trans hab
    have ha2 : 2 ≤ n / q := hR.trans haR
    have hb2 : 2 ≤ (n + H) / q := hR.trans hbR
    have hlogPower : ((m - 1 : ℕ) : ℝ) * Real.log (R : ℝ) ≤
        Real.log ((n / q : ℕ) : ℝ) := by
      have h : Real.log ((R ^ (m - 1) : ℕ) : ℝ) ≤
          Real.log ((n / q : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast haLower)
      simpa only [Nat.cast_pow, Real.log_pow] using h
    have hcoef : (m : ℝ) + 1 ≤ 2 * (m - 1 : ℕ) := by
      exact_mod_cast (show m + 1 ≤ 2 * (m - 1) by omega)
    have hloga : Real.log (X : ℝ) ≤ 2 * Real.log ((n / q : ℕ) : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hcoef hlogR.le
      nlinarith
    have hlogb : Real.log (X : ℝ) ≤ 2 * Real.log (((n + H) / q : ℕ) : ℝ) := by
      have h : Real.log ((n / q : ℕ) : ℝ) ≤
          Real.log (((n + H) / q : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast (show 0 < n / q by omega))
          (by exact_mod_cast hab)
      linarith
    have hqa : q * (n / q) ≤ 3 * X := by
      have h := Nat.div_mul_le_self n q
      nlinarith
    have hqb : q * ((n + H) / q) ≤ 3 * X := by
      have h := Nat.div_mul_le_self (n + H) q
      nlinarith
    exact prime_division_window_card_lower hX hnUpper hHX hq1
      ((Nat.mul_le_mul_left 8 hqR).trans hHR)
      (theta_endpoint_error_transfer hq1 ha2 hqa hloga hlogX hlength hlarge (htheta _ haR))
      (theta_endpoint_error_transfer hq1 hb2 hqb hlogb hlogX hlength hlarge (htheta _ hbR))
  have hcount := cofactor_sum_lower hlogX hRy htop hcounts
  have hharmonic := mul_le_mul_of_nonneg_left (log_le_reciprocal_sum R)
    (by positivity : 0 ≤ (H : ℝ) / (4 * Real.log (X : ℝ)))
  have hmPos : 0 < (m : ℝ) + 1 := by positivity
  have hratio : 1 / ((m : ℝ) + 1) ≤ Real.log (R : ℝ) / Real.log (X : ℝ) := by
    apply (div_le_div_iff₀ hmPos hlogX).mpr
    simpa only [one_mul, mul_comm] using hlogScale
  have hscalar := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ (H : ℝ) / 4)
  have hdeficit : (1 / (4 * ((m : ℝ) + 1))) * H ≤ ((nonsmoothWindow (R ^ (m - 1)) n H).card : ℝ) := by
    have heqLeft : (H : ℝ) / 4 * (1 / ((m : ℝ) + 1)) =
        (1 / (4 * ((m : ℝ) + 1))) * H := by
      field_simp [hmPos.ne'] <;> ring
    have heqRight : (H : ℝ) / 4 * (Real.log (R : ℝ) / Real.log (X : ℝ)) =
        (H : ℝ) / (4 * Real.log (X : ℝ)) * Real.log (R : ℝ) := by ring
    rw [heqLeft, heqRight] at hscalar
    exact hscalar.trans (hharmonic.trans hcount)
  exact long_average_le_of_nonsmooth_card (by omega) hdeficit

end JSP1006
