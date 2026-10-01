/-
JSP1006 / Erdos 1201: full original lower-density formulation.
UNCOMPILED DRAFT. No claim of formal verification or prize eligibility is made.
The set definition below matches the fixed formal-conjectures source at
 e04cc601840dd7a37f89b821a67f3a9e3c38d9c3, ErdosProblems/1201.lean.
That definition is Copyright 2026 The Formal Conjectures Authors, Apache-2.0.
All new analytic inputs are proved in the preceding source modules; the target
is not conditional on an MR assertion, density hypothesis, or proof oracle.
-/
import DyadicDensity

open scoped Classical

open Nat Filter Finset
open scoped Topology

namespace Erdos1201

noncomputable def Erdos1201Set (epsilon : ℝ) (k : ℕ) : Set ℕ :=
  {n : ℕ | ((sSup {p : ℕ | p.Prime ∧ p ∣ ∏ i ∈ range (k + 1), (n + i)} : ℕ) : ℝ) >
    (n : ℝ) ^ (1 - epsilon)}

open JSP1006

/-- A witnessed prime divisor in a positive shifted factor is at most the
largest prime divisor of the complete product, including its zeroth factor. -/
theorem goodStart_mem_Erdos1201Set {epsilon epsilon' : ℝ} {H n : ℕ}
    (hn : 0 < n) (hepsilon : epsilon' ≤ epsilon)
    (hgood : goodStart epsilon' H n) : n ∈ Erdos1201Set epsilon H := by
  classical
  obtain ⟨j, hj, p, hp, hpn, hlarge⟩ := hgood
  let Q := ∏ i ∈ range (H + 1), (n + i)
  have hQ : 0 < Q := by
    apply Finset.prod_pos
    intro i _
    omega
  have hjRange : j ∈ range (H + 1) := by
    have hj' := (Finset.mem_Icc.mp hj).2
    exact Finset.mem_range.mpr (by omega)
  have hpQ : p ∣ Q := hpn.trans (Finset.dvd_prod_of_mem (fun i => n + i) hjRange)
  have hbounded : BddAbove {q : ℕ | q.Prime ∧ q ∣ Q} :=
    ⟨Q, fun q hq => Nat.le_of_dvd hQ hq.2⟩
  have hsup : p ≤ sSup {q : ℕ | q.Prime ∧ q ∣ Q} := le_csSup hbounded ⟨hp, hpQ⟩
  have hthreshold : (n : ℝ) ^ (1 - epsilon) ≤ (n : ℝ) ^ (1 - epsilon') :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
  exact lt_of_lt_of_le (lt_of_le_of_lt hthreshold hlarge) (by exact_mod_cast hsup)

theorem goodStart_count_le_target_add_one {epsilon epsilon' : ℝ} (hepsilon : epsilon' ≤ epsilon)
    (H N : ℕ) :
    Nat.count (goodStart epsilon' H) N ≤ Nat.count (· ∈ Erdos1201Set epsilon H) N + 1 := by
  classical
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  have hsubset : (range N).filter (goodStart epsilon' H) ⊆
      insert 0 ((range N).filter (· ∈ Erdos1201Set epsilon H)) := by
    intro n hn
    obtain ⟨hnN, hgood⟩ := Finset.mem_filter.mp hn
    by_cases hn0 : n = 0
    · exact Finset.mem_insert.mpr (Or.inl hn0)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨hnN, goodStart_mem_Erdos1201Set (by omega) hepsilon hgood⟩))
  exact (Finset.card_le_card hsubset).trans (Finset.card_insert_le 0 _)

/-- A stronger eventual count formulation, with every epsilon,eta > 0.
The clamp to epsilon' <= 1/2 is only a stronger intermediate statement. -/
theorem erdos_1201_eventually :
    ∀ epsilon > 0, ∀ eta > 0, ∃ k : ℕ,
      ∀ᶠ x : ℕ in atTop,
        1 - eta ≤ (Nat.count (· ∈ Erdos1201Set epsilon k) x : ℝ) / x := by
  classical
  intro epsilon hepsilon eta heta
  let epsilon' := min epsilon (1 / 2)
  have hepsilon' : 0 < epsilon' := lt_min hepsilon (by norm_num)
  have hepsilon'One : epsilon' ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hepsilon'Le : epsilon' ≤ epsilon := min_le_left _ _
  obtain ⟨H, _hH, hdensity⟩ := exists_eventually_goodStart_density hepsilon' hepsilon'One
    (by positivity : (0 : ℝ) < eta / 2)
  have hi : Tendsto (fun x : ℕ => (x : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  refine ⟨H, ?_⟩
  filter_upwards [hdensity, eventually_ge_atTop 1,
    hi.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < eta / 2))]
    with x hd hx hsmall
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hc : (Nat.count (goodStart epsilon' H) x : ℝ) ≤
      (Nat.count (· ∈ Erdos1201Set epsilon H) x : ℝ) + 1 := by
    exact_mod_cast goodStart_count_le_target_add_one hepsilon'Le H x
  have hd' := (le_div_iff₀ hxR).mp hd
  have hs : (1 : ℝ) < eta / 2 * x := by
    rw [← one_div] at hsmall
    exact (div_lt_iff₀ hxR).mp hsmall
  apply (le_div_iff₀ hxR).mpr
  nlinarith

/-- Affirmative answer in the original full lower-density formulation. -/
theorem erdos_1201 :
    ∀ epsilon > 0, ∀ eta > 0, ∃ k : ℕ,
      atTop.liminf (fun x : ℕ =>
        (((Nat.count (· ∈ Erdos1201Set epsilon k) x : ℝ) / (x : ℝ)) : EReal)) ≥
          (1 - eta : EReal) := by
  classical
  intro epsilon hepsilon eta heta
  by_cases htop : eta = ⊤
  · refine ⟨0, ?_⟩
    rw [htop, EReal.sub_top]
    exact bot_le
  · have hbot : eta ≠ ⊥ := by
      intro h
      have hbad : (0 : EReal) < ⊥ := h ▸ heta
      exact (not_lt_of_ge bot_le) hbad
    have hpos : 0 < eta.toReal := EReal.toReal_pos heta htop
    have hcoe : (eta.toReal : EReal) = eta := EReal.coe_toReal htop hbot
    obtain ⟨k, hk⟩ := erdos_1201_eventually epsilon hepsilon eta.toReal hpos
    refine ⟨k, ?_⟩
    apply Filter.le_liminf_of_le (α := EReal) (h := ?_)
    filter_upwards [hk] with x hx
    simpa only [EReal.coe_sub, EReal.coe_one, EReal.coe_div, hcoe] using
      (EReal.coe_le_coe_iff.mpr hx)

end Erdos1201

#print axioms Erdos1201.erdos_1201
#print axioms Erdos1201.erdos_1201_eventually
