/- Finite prime-window estimates including division remainders. UNCOMPILED DRAFT. -/
import ThetaLogPower

open scoped Classical

open scoped BigOperators

namespace JSP1006

def primeInterval (a b : ℕ) : Finset ℕ := b.primesLE \ a.primesLE

theorem mem_primeInterval (a b p : ℕ) :
    p ∈ primeInterval a b ↔ a < p ∧ p ≤ b ∧ p.Prime := by
  simp only [primeInterval, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpb, hp⟩, hnot⟩
    exact ⟨lt_of_not_ge (fun hpa => hnot ⟨hpa, hp⟩), hpb, hp⟩
  · rintro ⟨hap, hpb, hp⟩
    exact ⟨⟨hpb, hp⟩, fun hpa => (not_le_of_gt hap) hpa.1⟩

theorem primeInterval_log_sum {a b : ℕ} (hab : a ≤ b) :
    (∑ p ∈ primeInterval a b, Real.log (p : ℝ)) =
      Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
  exact Finset.sum_sdiff_eq_sub (Nat.primesLE_mono hab)

theorem division_window_gap (n H q : ℕ) (hq : 0 < q) :
    (H : ℝ) / q - 1 ≤ (((n + H) / q : ℕ) : ℝ) - ((n / q : ℕ) : ℝ) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have h₀ : ((n % q : ℕ) : ℝ) + (q : ℝ) * (n / q : ℕ) = n := by
    exact_mod_cast Nat.mod_add_div n q
  have h₁ : (((n + H) % q : ℕ) : ℝ) + (q : ℝ) * ((n + H) / q : ℕ) =
      (n : ℝ) + H := by exact_mod_cast Nat.mod_add_div (n + H) q
  have hr₀ : (0 : ℝ) ≤ (n % q : ℕ) := Nat.cast_nonneg _
  have hr₁ : (((n + H) % q : ℕ) : ℝ) < q := by exact_mod_cast Nat.mod_lt (n + H) hq
  have hdiv : (H : ℝ) / q ≤ (((n + H) / q : ℕ) : ℝ) - (n / q : ℕ) + 1 := by
    apply (div_le_iff₀ hqr).mpr
    nlinarith
  linarith

theorem theta_division_window_lower {n H q : ℕ} (hq : 0 < q) (hH : 8 * q ≤ H)
    (ha : |Chebyshev.theta ((n / q : ℕ) : ℝ) - (n / q : ℕ)| ≤ (H : ℝ) / (8 * q))
    (hb : |Chebyshev.theta (((n + H) / q : ℕ) : ℝ) - ((n + H) / q : ℕ)| ≤
      (H : ℝ) / (8 * q)) :
    (H : ℝ) / (2 * q) ≤
      Chebyshev.theta (((n + H) / q : ℕ) : ℝ) - Chebyshev.theta ((n / q : ℕ) : ℝ) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hratio : (8 : ℝ) ≤ (H : ℝ) / q :=
    (le_div_iff₀ hqr).mpr (by exact_mod_cast hH)
  have hgap := division_window_gap n H q hq
  have ha' := (abs_le.mp ha).2
  have hb' := (abs_le.mp hb).1
  have he₁ : (H : ℝ) / (8 * q) = ((H : ℝ) / q) / 8 := by ring
  have he₂ : (H : ℝ) / (2 * q) = ((H : ℝ) / q) / 2 := by ring
  rw [he₁] at ha' hb'
  rw [he₂]
  linarith

theorem primeInterval_log_sum_upper {X a b : ℕ} (hX : 3 ≤ X) (hbX : b ≤ 3 * X) :
    (∑ p ∈ primeInterval a b, Real.log (p : ℝ)) ≤
      ((primeInterval a b).card : ℝ) * (2 * Real.log (X : ℝ)) := by
  have hlogX : Real.log 3 ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hX)
  calc
    _ ≤ ∑ _p ∈ primeInterval a b, 2 * Real.log (X : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨_, hpb, hpPrime⟩ := (mem_primeInterval a b p).mp hp
      have hlog := Real.log_le_log (by exact_mod_cast hpPrime.pos) (by
        exact_mod_cast hpb.trans hbX : (p : ℝ) ≤ 3 * X)
      rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
        (by exact_mod_cast (show X ≠ 0 by omega))] at hlog
      linarith
    _ = _ := by simp

/-- A lower bound for each cofactor's prime window. The analytic endpoint errors
are numerical bounds, to be discharged by theta_error_eventually_le_log_power. -/
theorem prime_division_window_card_lower {X n H q : ℕ}
    (hX : 3 ≤ X) (hn : n ≤ 2 * X) (hHX : H ≤ X)
    (hq : 0 < q) (hHq : 8 * q ≤ H)
    (ha : |Chebyshev.theta ((n / q : ℕ) : ℝ) - (n / q : ℕ)| ≤ (H : ℝ) / (8 * q))
    (hb : |Chebyshev.theta (((n + H) / q : ℕ) : ℝ) - ((n + H) / q : ℕ)| ≤
      (H : ℝ) / (8 * q)) :
    (H : ℝ) / (4 * q * Real.log (X : ℝ)) ≤
      ((primeInterval (n / q) ((n + H) / q)).card : ℝ) := by
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hab : n / q ≤ (n + H) / q := Nat.div_le_div_right (Nat.le_add_right n H)
  have hbX : (n + H) / q ≤ 3 * X := (Nat.div_le_self _ _).trans (by omega)
  have hlo := theta_division_window_lower hq hHq ha hb
  have hhi := primeInterval_log_sum_upper (a := n / q) hX hbX
  rw [primeInterval_log_sum hab] at hhi
  have hmain : (H : ℝ) / (2 * q) ≤
      ((primeInterval (n / q) ((n + H) / q)).card : ℝ) * (2 * Real.log (X : ℝ)) :=
    hlo.trans hhi
  have hscaled := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * q)).mp hmain
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * q * Real.log (X : ℝ))).mpr
  nlinarith

end JSP1006
