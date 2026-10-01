/- Exact cofactor-pair counting for the long-window deficit. UNCOMPILED DRAFT. -/
import Elementary
import PrimeWindow

open scoped Classical

open scoped BigOperators

namespace JSP1006

def primeCofactorPairs (n L R : ℕ) : Finset (Σ _q : ℕ, ℕ) :=
  (Finset.Icc 1 R).sigma (fun q => primeInterval (n / q) ((n + L) / q))

noncomputable def nonsmoothWindow (y n L : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc n (n + L)).filter (fun a => ¬ SmoothAt y a)

theorem mem_primeCofactorPairs (n L R : ℕ) (a : Σ _q : ℕ, ℕ) :
    a ∈ primeCofactorPairs n L R ↔
      1 ≤ a.1 ∧ a.1 ≤ R ∧ n / a.1 < a.2 ∧ a.2 ≤ (n + L) / a.1 ∧ a.2.Prime := by
  simp only [primeCofactorPairs, Finset.mem_sigma, Finset.mem_Icc,
    mem_primeInterval, and_assoc]

theorem primeCofactorPairs_product_bounds {n L R : ℕ} {a : Σ _q : ℕ, ℕ}
    (ha : a ∈ primeCofactorPairs n L R) : n < a.1 * a.2 ∧ a.1 * a.2 ≤ n + L := by
  obtain ⟨hq, _, hlo, hhi, _⟩ := (mem_primeCofactorPairs n L R a).mp ha
  constructor
  · simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hq).mp hlo
  · simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hq).mp hhi

theorem primeCofactorPairs_prime_gt {n L R y : ℕ} (hRy : R * y ≤ n)
    {a : Σ _q : ℕ, ℕ} (ha : a ∈ primeCofactorPairs n L R) : y < a.2 := by
  obtain ⟨_, hqR, _, _, _⟩ := (mem_primeCofactorPairs n L R a).mp ha
  have hlo := (primeCofactorPairs_product_bounds ha).1
  by_contra h
  have hpy : a.2 ≤ y := le_of_not_gt h
  have hprod := Nat.mul_le_mul hqR hpy
  omega

/-- The represented integer identifies both its large prime and its cofactor. -/
theorem primeCofactorPairs_product_injective {n L R y : ℕ}
    (hRy : R * y ≤ n) (hupper : n + L ≤ y * y) :
    Set.InjOn (fun a : Σ _q : ℕ, ℕ => a.1 * a.2) ↑(primeCofactorPairs n L R) := by
  intro a ha b hb heq
  obtain ⟨qa, pa⟩ := a
  obtain ⟨qb, pb⟩ := b
  change qa * pa = qb * pb at heq
  have hpa := ((mem_primeCofactorPairs n L R ⟨qa, pa⟩).mp ha).2.2.2.2
  have hpb := ((mem_primeCofactorPairs n L R ⟨qb, pb⟩).mp hb).2.2.2.2
  have hba := primeCofactorPairs_product_bounds ha
  have hprimeEq : pa = pb := large_prime_unique (by have := hba.1; omega)
    (hba.2.trans hupper) hpa hpb (primeCofactorPairs_prime_gt hRy ha)
    (primeCofactorPairs_prime_gt hRy hb) (dvd_mul_left pa qa) (by
      change pb ∣ qa * pa
      rw [heq]
      exact dvd_mul_left pb qb)
  subst pb
  have hqEq : qa = qb := Nat.eq_of_mul_eq_mul_right hpa.pos heq
  subst qb
  rfl

theorem primeCofactorPairs_card_le_nonsmooth {n L R y : ℕ}
    (hRy : R * y ≤ n) (hupper : n + L ≤ y * y) :
    (primeCofactorPairs n L R).card ≤ (nonsmoothWindow y n L).card := by
  classical
  let f : (Σ _q : ℕ, ℕ) → ℕ := fun a => a.1 * a.2
  have hsub : (primeCofactorPairs n L R).image f ⊆ nonsmoothWindow y n L := by
    intro a ha
    obtain ⟨qp, hqp, rfl⟩ := Finset.mem_image.mp ha
    have hb := primeCofactorPairs_product_bounds hqp
    have hprime := ((mem_primeCofactorPairs n L R qp).mp hqp).2.2.2.2
    have hgt := primeCofactorPairs_prime_gt hRy hqp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr hb, ?_⟩
    intro hs
    exact (not_le_of_gt hgt) (hs qp.2 hprime (dvd_mul_left qp.2 qp.1))
  calc
    (primeCofactorPairs n L R).card = ((primeCofactorPairs n L R).image f).card :=
      (Finset.card_image_of_injOn (primeCofactorPairs_product_injective hRy hupper)).symm
    _ ≤ (nonsmoothWindow y n L).card := Finset.card_le_card hsub

theorem cofactor_sum_lower {X n L R y : ℕ} (hlog : 0 < Real.log (X : ℝ))
    (hRy : R * y ≤ n) (hupper : n + L ≤ y * y)
    (hcount : ∀ q ∈ Finset.Icc 1 R,
      (L : ℝ) / (4 * q * Real.log (X : ℝ)) ≤
        ((primeInterval (n / q) ((n + L) / q)).card : ℝ)) :
    (L : ℝ) / (4 * Real.log (X : ℝ)) *
      (∑ q ∈ Finset.Icc 1 R, (1 : ℝ) / q) ≤ (nonsmoothWindow y n L).card := by
  have hsum :
      (∑ q ∈ Finset.Icc 1 R, (L : ℝ) / (4 * q * Real.log (X : ℝ))) ≤
        ((primeCofactorPairs n L R).card : ℝ) := by
    rw [primeCofactorPairs, Finset.card_sigma, Nat.cast_sum]
    exact Finset.sum_le_sum hcount
  have heq :
      (L : ℝ) / (4 * Real.log (X : ℝ)) *
        (∑ q ∈ Finset.Icc 1 R, (1 : ℝ) / q) =
      ∑ q ∈ Finset.Icc 1 R, (L : ℝ) / (4 * q * Real.log (X : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by have := (Finset.mem_Icc.mp hq).1; omega)
    field_simp [hq0, hlog.ne']
  rw [heq]
  exact hsum.trans (by exact_mod_cast primeCofactorPairs_card_le_nonsmooth hRy hupper)

theorem real_sum_shifts_eq_interval (f : ℕ → ℝ) (n L : ℕ) :
    (∑ j ∈ Finset.Icc 1 L, f (n + j)) = ∑ a ∈ Finset.Ioc n (n + L), f a := by
  apply Finset.sum_bij (fun j _ => n + j)
  · intro j hj
    have := Finset.mem_Icc.mp hj
    apply Finset.mem_Ioc.mpr
    omega
  · intro i _ j _ hij
    omega
  · intro a ha
    have := Finset.mem_Ioc.mp ha
    refine ⟨a - n, Finset.mem_Icc.mpr ?_, ?_⟩ <;> omega
  · intro j _
    rfl

theorem nonsmoothWindow_card_eq_deficit (y n L : ℕ) :
    ((nonsmoothWindow y n L).card : ℝ) =
      (L : ℝ) - ∑ j ∈ Finset.Icc 1 L, smoothIndicator y (n + j) := by
  classical
  have hone (a : ℕ) : (if ¬ SmoothAt y a then (1 : ℝ) else 0) = 1 - smoothIndicator y a := by
    by_cases h : SmoothAt y a <;> simp [smoothIndicator, h]
  calc
    _ = ∑ _a ∈ nonsmoothWindow y n L, (1 : ℝ) := by simp
    _ = ∑ a ∈ Finset.Ioc n (n + L), (1 - smoothIndicator y a) := by
      rw [nonsmoothWindow, Finset.sum_filter]
      exact Finset.sum_congr rfl (fun a _ => hone a)
    _ = (L : ℝ) - ∑ a ∈ Finset.Ioc n (n + L), smoothIndicator y a := by
      rw [Finset.sum_sub_distrib]
      simp
    _ = _ := by rw [real_sum_shifts_eq_interval]

theorem long_average_le_of_nonsmooth_card {y n L : ℕ} (hL : 0 < L)
    {gamma : ℝ} (hcount : gamma * L ≤ ((nonsmoothWindow y n L).card : ℝ)) :
    (∑ j ∈ Finset.Icc 1 L, smoothIndicator y (n + j)) / L ≤ 1 - gamma := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  rw [nonsmoothWindow_card_eq_deficit] at hcount
  apply (div_le_iff₀ hLR).mpr
  nlinarith

end JSP1006
