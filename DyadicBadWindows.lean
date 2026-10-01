/- Uniform bad-window counts on EVERY sufficiently large dyadic annulus.
   UNCOMPILED DRAFT. -/
import OriginalThreshold

open scoped Classical

open Filter
open scoped BigOperators Topology

namespace JSP1006
noncomputable section

theorem succ_le_two_pow (j : ℕ) : j + 1 ≤ 2 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih => rw [pow_succ]; omega

/-- Euclidean division of the exponent retains every dyadic scale. -/
theorem dyadic_integer_scale (m j : ℕ) (hm : 0 < m) :
    let R := 2 ^ (j / m)
    R ^ m ≤ 2 ^ j ∧ 2 ^ j ≤ 2 ^ m * R ^ m := by
  dsimp
  have hdecomp : j = j % m + (j / m) * m := by
    simpa only [Nat.mul_comm] using (Nat.mod_add_div j m).symm
  have hidentity : 2 ^ j = 2 ^ (j % m) * (2 ^ (j / m)) ^ m := by
    rw [← pow_mul, ← pow_add, ← hdecomp]
  have hmod := Nat.mod_lt j hm
  constructor
  · rw [hidentity]
    have hone : 1 ≤ 2 ^ (j % m) := Nat.one_le_pow _ _ (by norm_num)
    simpa only [one_mul] using Nat.mul_le_mul_right ((2 ^ (j / m)) ^ m) hone
  · rw [hidentity]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hmod.le)

/-- For each positive exponent loss and error tolerance there is one fixed H
which works on all sufficiently large dyadic annuli. -/
theorem exists_bad_dyadic_bound {epsilon alpha : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon ≤ 1) (halpha : 0 < alpha) :
    ∃ H J₀ : ℕ, 0 < H ∧ ∀ j : ℕ, J₀ ≤ j →
      (((Finset.Ioc (2 ^ j) (2 ^ (j + 1))).filter
        (fun n => ¬ goodStart epsilon H n)).card : ℝ) ≤ alpha * 2 ^ j := by
  classical
  let m := max 3 ⌈2 / epsilon⌉₊
  have hm : 3 ≤ m := le_max_left _ _
  have hmpos : 0 < m := by omega
  have hmEpsilon : 2 ≤ (m : ℝ) * epsilon := by
    apply (div_le_iff₀ hepsilon).mp
    exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 3 ⌈2 / epsilon⌉₊))
  let C := 2 ^ m
  have hC : 0 < C := by dsimp [C]; positivity
  let gamma : ℝ := 1 / (4 * ((m : ℝ) + 1))
  have hgamma : 0 < gamma := by dsimp [gamma]; positivity
  obtain ⟨H, hH, hcompare⟩ := real_twoLength_comparison (mul_pos halpha (sq_pos_of_pos hgamma))
  obtain ⟨X₀, hcompareX⟩ := eventually_atTop.mp (hcompare H le_rfl)
  obtain ⟨R₀, _hR₀, hlong⟩ := exists_uniform_long_average_deficit m C hm
  let R₁ := max R₀ (2 * C)
  let J₀ := max X₀ (m * R₁)
  refine ⟨H, J₀, hH, ?_⟩
  intro j hj
  let X := 2 ^ j
  let R := 2 ^ (j / m)
  let y := R ^ (m - 1)
  have hX₀ : X₀ ≤ X := by
    have hjX : X₀ ≤ j := (le_max_left _ _).trans hj
    exact hjX.trans (by have h := succ_le_two_pow j; dsimp [X]; omega)
  have hR₁ : R₁ ≤ R := by
    have hdiv : R₁ ≤ j / m := (Nat.le_div_iff_mul_le hmpos).mpr
      (by have h := (le_max_right X₀ (m * R₁)).trans hj; simpa [mul_comm] using h)
    exact hdiv.trans (by have h := succ_le_two_pow (j / m); dsimp [R]; omega)
  have hR₀ : R₀ ≤ R := (le_max_left _ _).trans hR₁
  have hRC : 2 * C ≤ R := (le_max_right _ _).trans hR₁
  obtain ⟨hscale, hupper⟩ := dyadic_integer_scale m j hmpos
  change R ^ m ≤ X at hscale
  change X ≤ C * R ^ m at hupper
  obtain ⟨hL, hLX, hlongX⟩ := hlong R hR₀ X hscale hupper
  obtain ⟨_hL', _hHL, _hLX', henergy⟩ := hcompareX X hX₀
  have henergyY := henergy (smoothComplex y) (smoothComplex_multiplicative y)
    (fun n _ => smoothComplex_real y n) (fun n _ => smoothComplex_bound y n)
  have hthreshold (n : ℕ) (hn : n ∈ Finset.Ioc X (2 * X)) :
      (n : ℝ) ^ (1 - epsilon) ≤ y := by
    apply original_threshold_le_integer_cutoff hepsilon hepsilonOne hm hC hmEpsilon hRC
    have hnUpper := (Finset.mem_Ioc.mp hn).2
    nlinarith
  have hlongAll (n : ℕ) (hn : n ∈ Finset.Ioc X (2 * X)) :
      (∑ a ∈ Finset.Icc 1 (longLength X), smoothIndicator y (n + a)) / longLength X ≤ 1 - gamma := by
    have hn' := Finset.mem_Ioc.mp hn
    exact hlongX n hn'.1.le hn'.2
  have hcount := bad_dyadic_card_le_of_energy hH hgamma hthreshold hlongAll henergyY
  have hcount' : (((Finset.Ioc X (2 * X)).filter
      (fun n => ¬ goodStart epsilon H n)).card : ℝ) ≤ alpha * X := by
    apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hgamma)).mp
    nlinarith only [hcount]
  simpa only [X, pow_succ, Nat.mul_comm, Nat.cast_pow, Nat.cast_ofNat] using hcount'

end
end JSP1006
