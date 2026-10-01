/- Original n-dependent threshold and its reduction to a fixed smooth cutoff.
   UNCOMPILED DRAFT. -/
import RealTwoLengthComparison

open scoped Classical

open Filter
open scoped BigOperators ComplexConjugate Topology
open Erdos67b

namespace JSP1006
noncomputable section

def goodStart (epsilon : ℝ) (H n : ℕ) : Prop :=
  ∃ j ∈ Finset.Icc 1 H, ∃ p : ℕ, p.Prime ∧ p ∣ n + j ∧ (n : ℝ) ^ (1 - epsilon) < p

def smoothComplex (y n : ℕ) : ℂ := (smoothIndicator y n : ℂ)

theorem smoothComplex_multiplicative (y : ℕ) : IsMultiplicativeOnPositiveNat (smoothComplex y) := by
  refine ⟨by simp [smoothComplex, smoothIndicator_one], ?_⟩
  intro a b _ _ _
  simp [smoothComplex, smoothIndicator_mul]

theorem smoothComplex_real (y n : ℕ) : conj (smoothComplex y n) = smoothComplex y n := by
  simp [smoothComplex]

theorem smoothComplex_bound (y n : ℕ) : ‖smoothComplex y n‖ ≤ 1 := by
  rw [smoothComplex, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (smoothIndicator_bounds y n).1]
  exact (smoothIndicator_bounds y n).2

theorem shortAverage_smoothComplex (y n H : ℕ) :
    shortAverage (smoothComplex y) n H =
      (((∑ j ∈ Finset.Icc 1 H, smoothIndicator y (n + j)) / H : ℝ) : ℂ) := by
  simp [shortAverage, smoothComplex]

/-- Integer-power cutoff geometry; the factor 2C is retained explicitly. -/
theorem original_threshold_le_integer_cutoff {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilonOne : epsilon ≤ 1) {m C R n : ℕ} (hm : 3 ≤ m) (hC : 0 < C)
    (hmEpsilon : 2 ≤ (m : ℝ) * epsilon) (hR : 2 * C ≤ R)
    (hn : n ≤ 2 * C * R ^ m) :
    (n : ℝ) ^ (1 - epsilon) ≤ (R ^ (m - 1) : ℕ) := by
  have hRone : (1 : ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
  have hCOne : (1 : ℝ) ≤ 2 * C := by exact_mod_cast (show 1 ≤ 2 * C by omega)
  have hRR : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hRone
  have ha : 0 ≤ 1 - epsilon := by linarith
  have haOne : 1 - epsilon ≤ 1 := by linarith
  have hexp : (m : ℝ) * (1 - epsilon) ≤ ((m - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 2 ≤ m)]
    push_cast
    nlinarith
  calc
    (n : ℝ) ^ (1 - epsilon) ≤ ((2 : ℝ) * C * (R : ℝ) ^ m) ^ (1 - epsilon) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn) ha
    _ = ((2 : ℝ) * C) ^ (1 - epsilon) * (R : ℝ) ^ ((m : ℝ) * (1 - epsilon)) := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_mul hRR.le]
    _ ≤ ((2 : ℝ) * C) * (R : ℝ) ^ ((m - 2 : ℕ) : ℝ) :=
      mul_le_mul (Real.rpow_le_self_of_one_le hCOne haOne)
        (Real.rpow_le_rpow_of_exponent_le hRone hexp) (by positivity) (by positivity)
    _ ≤ (R : ℝ) * (R : ℝ) ^ ((m - 2 : ℕ) : ℝ) := by gcongr; exact_mod_cast hR
    _ = (R ^ (m - 1) : ℕ) := by
      rw [Real.rpow_natCast, Nat.cast_pow]
      have hmEq : m - 1 = (m - 2) + 1 := by omega
      rw [hmEq, pow_succ]; ring

theorem not_goodStart_smooth {epsilon : ℝ} {H n y : ℕ}
    (hthreshold : (n : ℝ) ^ (1 - epsilon) ≤ y) (hbad : ¬ goodStart epsilon H n) :
    ∀ j ∈ Finset.Icc 1 H, SmoothAt y (n + j) := by
  intro j hj p hp hpn
  have hle : (p : ℝ) ≤ (n : ℝ) ^ (1 - epsilon) := by
    by_contra h
    exact hbad ⟨j, hj, p, hp, hpn, lt_of_not_ge h⟩
  exact_mod_cast hle.trans hthreshold

theorem bad_start_has_gap {epsilon gamma : ℝ} {H L n y : ℕ}
    (hH : 0 < H) (hgamma : 0 < gamma)
    (hthreshold : (n : ℝ) ^ (1 - epsilon) ≤ y)
    (hbad : ¬ goodStart epsilon H n)
    (hlong : (∑ j ∈ Finset.Icc 1 L, smoothIndicator y (n + j)) / L ≤ 1 - gamma) :
    gamma ^ 2 ≤ Complex.normSq
      (shortAverage (smoothComplex y) n H - shortAverage (smoothComplex y) n L) := by
  have hs := not_goodStart_smooth hthreshold hbad
  have hshort : (∑ j ∈ Finset.Icc 1 H, smoothIndicator y (n + j)) / H = 1 :=
    short_average_eq_one _ n H hH (by intro j hj; simp [smoothIndicator, hs j hj])
  rw [shortAverage_smoothComplex, shortAverage_smoothComplex, hshort, ← Complex.ofReal_sub,
    Complex.normSq_ofReal, ← pow_two]
  have hgap : gamma ≤ 1 - (∑ j ∈ Finset.Icc 1 L, smoothIndicator y (n + j)) / L := by linarith
  exact pow_le_pow_left₀ hgamma.le hgap 2

theorem bad_dyadic_card_le_of_energy {epsilon gamma zeta : ℝ} {H L X y : ℕ}
    (hH : 0 < H) (hgamma : 0 < gamma)
    (hthreshold : ∀ n ∈ Finset.Ioc X (2 * X), (n : ℝ) ^ (1 - epsilon) ≤ y)
    (hlong : ∀ n ∈ Finset.Ioc X (2 * X),
      (∑ j ∈ Finset.Icc 1 L, smoothIndicator y (n + j)) / L ≤ 1 - gamma)
    (henergy : twoLengthEnergy (smoothComplex y) X H L ≤ zeta * X) :
    (((Finset.Ioc X (2 * X)).filter (fun n => ¬ goodStart epsilon H n)).card : ℝ) * gamma ^ 2 ≤
      zeta * X := by
  classical
  let S := Finset.Ioc X (2 * X)
  let B := S.filter (fun n => ¬ goodStart epsilon H n)
  calc
    (B.card : ℝ) * gamma ^ 2 = ∑ _n ∈ B, gamma ^ 2 := by simp
    _ ≤ ∑ n ∈ B, Complex.normSq
        (shortAverage (smoothComplex y) n H - shortAverage (smoothComplex y) n L) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := Finset.mem_filter.mp hn
      exact bad_start_has_gap hH hgamma (hthreshold n hn'.1) hn'.2 (hlong n hn'.1)
    _ ≤ twoLengthEnergy (smoothComplex y) X H L := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro n _ _
      exact Complex.normSq_nonneg _
    _ ≤ zeta * X := henergy

end
end JSP1006
