/-
Elementary infrastructure for JSP1006 / Erdos 1201.
This file is a draft and has NOT been compiled in this environment.
It does not state or claim the unresolved formal MR input or the final theorem.
-/
import Mathlib

open scoped Classical

open scoped BigOperators

namespace JSP1006

/-- Every prime divisor of n is at most the fixed cutoff y. -/
def SmoothAt (y n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ≤ y

theorem smoothAt_one (y : ℕ) : SmoothAt y 1 := by
  intro p hp hpd
  have hp1 : p = 1 := Nat.dvd_one.mp hpd
  have hp2 := hp.two_le
  omega

theorem smoothAt_mul_iff (y a b : ℕ) :
    SmoothAt y (a * b) ↔ SmoothAt y a ∧ SmoothAt y b := by
  constructor
  · intro h
    constructor
    · intro p hp hpa
      exact h p hp (dvd_mul_of_dvd_left hpa b)
    · intro p hp hpb
      exact h p hp (dvd_mul_of_dvd_right hpb a)
  · rintro ⟨ha, hb⟩ p hp hpd
    rcases hp.dvd_mul.mp hpd with hpa | hpb
    · exact ha p hp hpa
    · exact hb p hp hpb

noncomputable def smoothIndicator (y n : ℕ) : ℝ := by
  classical
  exact if SmoothAt y n then 1 else 0

theorem smoothIndicator_one (y : ℕ) : smoothIndicator y 1 = 1 := by
  simp [smoothIndicator, smoothAt_one]

theorem smoothIndicator_zero_or_one (y n : ℕ) :
    smoothIndicator y n = 0 ∨ smoothIndicator y n = 1 := by
  classical
  by_cases h : SmoothAt y n <;> simp [smoothIndicator, h]

theorem smoothIndicator_mul (y a b : ℕ) :
    smoothIndicator y (a * b) = smoothIndicator y a * smoothIndicator y b := by
  classical
  by_cases ha : SmoothAt y a <;> by_cases hb : SmoothAt y b <;>
    simp [smoothIndicator, smoothAt_mul_iff, ha, hb]

theorem smoothIndicator_bounds (y n : ℕ) :
    0 ≤ smoothIndicator y n ∧ smoothIndicator y n ≤ 1 := by
  rcases smoothIndicator_zero_or_one y n with h | h <;> rw [h] <;> norm_num

/-- A positive integer at most y squared cannot have two different prime divisors above y. -/
theorem large_prime_unique {y n p q : ℕ}
    (hn0 : 0 < n) (hn : n ≤ y * y)
    (hp : p.Prime) (hq : q.Prime) (hyp : y < p) (hyq : y < q)
    (hpn : p ∣ n) (hqn : q ∣ n) : p = q := by
  by_contra hpq
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hprod : p * q ∣ n := hcop.mul_dvd_of_dvd_of_dvd hpn hqn
  have hle : p * q ≤ n := Nat.le_of_dvd hn0 hprod
  nlinarith

def largePrimeDivisors (X y n : ℕ) : Finset ℕ :=
  ((2 * X).primesLE).filter (fun p => y < p ∧ p ∣ n)

theorem mem_largePrimeDivisors_iff (X y n p : ℕ) :
    p ∈ largePrimeDivisors X y n ↔
      p ≤ 2 * X ∧ p.Prime ∧ y < p ∧ p ∣ n := by
  simp [largePrimeDivisors, Nat.mem_primesLE, and_assoc]

/-- The prime count is exactly the complement of the smoothness indicator in this range. -/
theorem largePrimeDivisors_card (X y n : ℕ)
    (hn0 : 0 < n) (hnX : n ≤ 2 * X) (hXy : 2 * X ≤ y * y) :
    ((largePrimeDivisors X y n).card : ℝ) = 1 - smoothIndicator y n := by
  classical
  by_cases hs : SmoothAt y n
  · have hempty : largePrimeDivisors X y n = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨_, hpPrime, hyp, hpn⟩ := (mem_largePrimeDivisors_iff X y n p).mp hp
      exact (not_lt_of_ge (hs p hpPrime hpn)) hyp
    simp [hempty, smoothIndicator, hs]
  · have hex : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ y < p := by
      by_contra h
      apply hs
      intro p hp hpn
      by_contra hle
      exact h ⟨p, hp, hpn, lt_of_not_ge hle⟩
    obtain ⟨p, hp, hpn, hyp⟩ := hex
    have hpX : p ≤ 2 * X := (Nat.le_of_dvd hn0 hpn).trans hnX
    have hpMem : p ∈ largePrimeDivisors X y n :=
      (mem_largePrimeDivisors_iff X y n p).mpr ⟨hpX, hp, hyp, hpn⟩
    have hsingle : largePrimeDivisors X y n = {p} := by
      ext q
      constructor
      · intro hqMem
        obtain ⟨_, hq, hyq, hqn⟩ := (mem_largePrimeDivisors_iff X y n q).mp hqMem
        have heq : q = p := large_prime_unique hn0 (hnX.trans hXy) hq hp hyq hyp hqn hpn
        simpa [heq]
      · intro hq
        have heq : q = p := Finset.mem_singleton.mp hq
        simpa [heq] using hpMem
    simp [hsingle, smoothIndicator, hs]

/-- An exact double-counting identity, before replacing divisibility counts by floors. -/
theorem smooth_complement_sum_eq_divisibility_counts (X y : ℕ)
    (hXy : 2 * X ≤ y * y) :
    (∑ n ∈ Finset.Ioc X (2 * X), (1 - smoothIndicator y n)) =
      ∑ p ∈ ((2 * X).primesLE).filter (y < ·),
        (((Finset.Ioc X (2 * X)).filter (p ∣ ·)).card : ℝ) := by
  classical
  have hone (n : ℕ) (hn : n ∈ Finset.Ioc X (2 * X)) :
      1 - smoothIndicator y n =
        ∑ p ∈ (2 * X).primesLE, if y < p ∧ p ∣ n then (1 : ℝ) else 0 := by
    have hnBounds := Finset.mem_Ioc.mp hn
    have hcard := largePrimeDivisors_card X y n (by omega) hnBounds.2 hXy
    rw [← hcard]
    calc
      ((largePrimeDivisors X y n).card : ℝ) =
          ∑ _p ∈ largePrimeDivisors X y n, (1 : ℝ) := by simp
      _ = _ := by rw [largePrimeDivisors, Finset.sum_filter]
  calc
    _ = ∑ n ∈ Finset.Ioc X (2 * X),
          ∑ p ∈ (2 * X).primesLE, if y < p ∧ p ∣ n then (1 : ℝ) else 0 :=
      Finset.sum_congr rfl hone
    _ = ∑ p ∈ (2 * X).primesLE,
          ∑ n ∈ Finset.Ioc X (2 * X), if y < p ∧ p ∣ n then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : y < p
      · simp only [hp, true_and, if_true]
        rw [← Finset.sum_filter]
        simp
      · simp [hp]

/-- An exact exceptional-set estimate; this is finite algebra, not an MR theorem. -/
theorem card_sq_le_sum_sq {ι : Type*} [DecidableEq ι]
    (S E : Finset ι) (z : ι → ℝ) (d : ℝ)
    (hES : E ⊆ S) (hd : 0 ≤ d) (hE : ∀ x ∈ E, d ≤ |z x|) :
    (E.card : ℝ) * d ^ 2 ≤ ∑ x ∈ S, (z x) ^ 2 := by
  calc
    (E.card : ℝ) * d ^ 2 = ∑ _x ∈ E, d ^ 2 := by simp
    _ ≤ ∑ x ∈ E, (z x) ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      have h := hE x hx
      have hs := sq_abs (z x)
      nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg (abs_nonneg (z x)) hd)]
    _ ≤ ∑ x ∈ S, (z x) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hES (by
        intro x _ _
        exact sq_nonneg _)

/-- If all short-window values are 1, their normalized sum is 1. -/
theorem short_average_eq_one (f : ℕ → ℝ) (n H : ℕ) (hH : 0 < H)
    (hf : ∀ j ∈ Finset.Icc 1 H, f (n + j) = 1) :
    (∑ j ∈ Finset.Icc 1 H, f (n + j)) / H = 1 := by
  have hs : (∑ j ∈ Finset.Icc 1 H, f (n + j)) = (H : ℝ) := by
    calc
      (∑ j ∈ Finset.Icc 1 H, f (n + j)) = ∑ _j ∈ Finset.Icc 1 H, (1 : ℝ) :=
        Finset.sum_congr rfl hf
      _ = H := by simp
  rw [hs]
  exact div_self (by exact_mod_cast hH.ne')

/-- The deterministic implication used to place a bad window in the exceptional set. -/
theorem unit_average_deviation {M gamma : ℝ} (hgamma : 0 < gamma)
    (hM : M ≤ 1 - 3 * gamma / 4) : gamma / 2 < |1 - M| := by
  have h : 0 ≤ 1 - M := by linarith
  rw [abs_of_nonneg h]
  linarith

end JSP1006
