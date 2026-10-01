/- Dyadic counting, including the nonsparse-to-prefix passage. UNCOMPILED DRAFT. -/
import DyadicBadWindows

open scoped Classical

open Filter
open scoped BigOperators Topology

namespace JSP1006
noncomputable section

theorem exists_dyadic_cover : ∀ N : ℕ, 0 < N → ∃ j : ℕ, 2 ^ j ≤ N ∧ N < 2 ^ (j + 1) := by
  intro N
  induction N with
  | zero => intro h; omega
  | succ N ih =>
    intro h
    by_cases hzero : N = 0
    · subst N; exact ⟨0, by norm_num, by norm_num⟩
    · obtain ⟨j, hj, hj'⟩ := ih (by omega)
      by_cases hnext : N + 1 < 2 ^ (j + 1)
      · exact ⟨j, by omega, hnext⟩
      · have heq : N + 1 = 2 ^ (j + 1) := by omega
        refine ⟨j + 1, heq.ge, ?_⟩
        rw [heq, pow_succ]
        have hp : 0 < 2 ^ (j + 1) := by positivity
        omega

theorem filtered_prefix_split (P : ℕ → Prop) (A B : ℕ) (hAB : A ≤ B) :
    ((Finset.Ioc 0 B).filter P).card =
      ((Finset.Ioc 0 A).filter P).card + ((Finset.Ioc A B).filter P).card := by
  classical
  have hu := Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le A) hAB
  rw [← hu, Finset.filter_union, Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro n hn₁ hn₂
  have h₁ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn₁).1
  have h₂ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn₂).1
  omega

theorem filtered_dyadic_prefix_le (P : ℕ → Prop) {alpha : ℝ} (halpha : 0 ≤ alpha)
    (J₀ : ℕ) (hdyadic : ∀ j : ℕ, J₀ ≤ j →
      (((Finset.Ioc (2 ^ j) (2 ^ (j + 1))).filter P).card : ℝ) ≤ alpha * 2 ^ j) :
    ∀ j : ℕ, (((Finset.Ioc 0 (2 ^ j)).filter P).card : ℝ) ≤
      (2 : ℝ) ^ J₀ + alpha * 2 ^ j := by
  classical
  have htrivial (j : ℕ) : (((Finset.Ioc 0 (2 ^ j)).filter P).card : ℝ) ≤ (2 : ℝ) ^ j := by
    have h := Finset.card_le_card (Finset.filter_subset P (Finset.Ioc 0 (2 ^ j)))
    simpa only [Nat.card_Ioc, Nat.sub_zero, Nat.cast_pow, Nat.cast_ofNat] using
      (show (((Finset.Ioc 0 (2 ^ j)).filter P).card : ℝ) ≤ ((Finset.Ioc 0 (2 ^ j)).card : ℝ) by exact_mod_cast h)
  intro j
  induction j with
  | zero =>
    have hJ : (1 : ℝ) ≤ 2 ^ J₀ := one_le_pow₀ (by norm_num)
    have ht := htrivial 0
    simp only [pow_zero] at ht ⊢
    nlinarith
  | succ j ih =>
    by_cases hj : J₀ ≤ j
    · have hp : 2 ^ j ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [filtered_prefix_split P (2 ^ j) (2 ^ (j + 1)) hp, Nat.cast_add]
      have hd := hdyadic j hj
      simp only [pow_succ] at hd ⊢
      nlinarith
    · have hj' : j + 1 ≤ J₀ := by omega
      have hpow : (2 : ℝ) ^ (j + 1) ≤ 2 ^ J₀ := pow_le_pow_right₀ (by norm_num) hj'
      have ht := htrivial (j + 1)
      have hpos : 0 ≤ alpha * (2 : ℝ) ^ (j + 1) := by positivity
      linarith

/-- Arbitrary prefixes cost at most the factor two from their dyadic cover.
The extra 1 explicitly accounts for the natural number zero. -/
theorem filtered_range_le_of_dyadic (P : ℕ → Prop) {alpha : ℝ} (halpha : 0 ≤ alpha)
    (J₀ : ℕ) (hdyadic : ∀ j : ℕ, J₀ ≤ j →
      (((Finset.Ioc (2 ^ j) (2 ^ (j + 1))).filter P).card : ℝ) ≤ alpha * 2 ^ j)
    {N : ℕ} (hN : 0 < N) :
    (((Finset.range N).filter P).card : ℝ) ≤ 1 + (2 : ℝ) ^ J₀ + 2 * alpha * N := by
  classical
  obtain ⟨j, hj, hj'⟩ := exists_dyadic_cover N hN
  have hsubset : (Finset.range N).filter P ⊆ insert 0 ((Finset.Ioc 0 (2 ^ (j + 1))).filter P) := by
    intro n hn
    obtain ⟨hnN, hnP⟩ := Finset.mem_filter.mp hn
    have hnN' := Finset.mem_range.mp hnN
    by_cases hn0 : n = 0
    · exact Finset.mem_insert.mpr (Or.inl hn0)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, hnP⟩))
  have hcard := (Finset.card_le_card hsubset).trans (Finset.card_insert_le 0 _)
  have hcardR : (((Finset.range N).filter P).card : ℝ) ≤
      (((Finset.Ioc 0 (2 ^ (j + 1))).filter P).card : ℝ) + 1 := by exact_mod_cast hcard
  have hpref := filtered_dyadic_prefix_le P halpha J₀ hdyadic (j + 1)
  have hpow : (2 : ℝ) ^ (j + 1) ≤ 2 * N := by
    rw [pow_succ]
    have h := (show (2 : ℝ) ^ j ≤ N by exact_mod_cast hj)
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hpow halpha
  linarith

/-- A full lower-density bound for prime witnesses, stronger than a liminf assertion. -/
theorem exists_eventually_goodStart_density {epsilon eta : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon ≤ 1) (heta : 0 < eta) :
    ∃ H : ℕ, 0 < H ∧ ∀ᶠ N : ℕ in atTop,
      1 - eta ≤ (Nat.count (goodStart epsilon H) N : ℝ) / N := by
  classical
  obtain ⟨H, J₀, hH, hbad⟩ := exists_bad_dyadic_bound hepsilon hepsilonOne
    (by positivity : (0 : ℝ) < eta / 4)
  let C : ℝ := 1 + 2 ^ J₀
  have hlim : Tendsto (fun N : ℕ => C / N) atTop (𝓝 0) := by
    have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa only [div_eq_mul_inv, mul_zero] using hi.const_mul C
  refine ⟨H, hH, ?_⟩
  filter_upwards [eventually_ge_atTop 1,
    hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < eta / 2))] with N hN hsmall
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hcount := filtered_range_le_of_dyadic (fun n => ¬ goodStart epsilon H n)
    (by positivity : (0 : ℝ) ≤ eta / 4) J₀
    (by intro j hj; convert hbad j hj using 1 <;> congr)
    (by omega : 0 < N)
  have hcount' : (((Finset.range N).filter (fun n => ¬ goodStart epsilon H n)).card : ℝ) ≤
      1 + (2 : ℝ) ^ J₀ + 2 * (eta / 4) * N := by
    convert hcount using 1 <;> congr
  have htotal := Finset.card_filter_add_card_filter_not
    (s := Finset.range N) (p := goodStart epsilon H)
  have htotalR : (((Finset.range N).filter (goodStart epsilon H)).card : ℝ) +
      (((Finset.range N).filter (fun n => ¬ goodStart epsilon H n)).card : ℝ) = N := by
    exact_mod_cast (by simpa only [Finset.card_range] using htotal)
  have hsmall' := (div_lt_iff₀ hNR).mp hsmall
  rw [Nat.count_eq_card_filter_range]
  apply (le_div_iff₀ hNR).mpr
  change (1 - eta) * (N : ℝ) ≤ (((Finset.range N).filter (goodStart epsilon H)).card : ℝ)
  dsimp only [C] at hsmall'
  nlinarith only [hcount', htotalR, hsmall']

end
end JSP1006
