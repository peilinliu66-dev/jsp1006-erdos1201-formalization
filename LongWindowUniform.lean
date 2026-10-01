/- Uniform asymptotic scale choices for the long-window deficit. UNCOMPILED DRAFT. -/
import LongWindowDeficit

open scoped Classical

open Filter
open scoped BigOperators Topology

namespace JSP1006

noncomputable def longLength (X : ℕ) : ℕ :=
  ⌊(X : ℝ) / Real.log (X : ℝ) ^ 16⌋₊

theorem eventually_longLength_properties :
    ∀ᶠ X : ℕ in atTop,
      3 ≤ X ∧ 0 < longLength X ∧ longLength X ≤ X ∧
      (X : ℝ) ≤ 2 * longLength X * Real.log (X : ℝ) ^ 16 ∧
      48 * (2 : ℝ) ^ 40 ≤ Real.log (X : ℝ) ^ 24 ∧
      ∀ R : ℕ, R ^ 2 ≤ X → 8 * R ≤ longLength X := by
  have hlogTop : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 3,
    hlogTop.eventually (eventually_ge_atTop (48 * (2 : ℝ) ^ 40 + 1)),
    (log_pow_div_sqrt_tendsto 16).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 32))]
    with X hX hlogLarge hsmall
  have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlogOne : 1 ≤ Real.log (X : ℝ) := by
    have hnonneg : (0 : ℝ) ≤ 48 * 2 ^ 40 := by positivity
    linarith
  have hlog : 0 < Real.log (X : ℝ) := lt_of_lt_of_le zero_lt_one hlogOne
  have hpow : 0 < Real.log (X : ℝ) ^ 16 := pow_pos hlog 16
  have hpowOne : 1 ≤ Real.log (X : ℝ) ^ 16 := one_le_pow₀ hlogOne
  have hsqrt : 0 < Real.sqrt (X : ℝ) := Real.sqrt_pos.mpr hXR
  have hsqrtOne : 1 ≤ Real.sqrt (X : ℝ) := by
    exact Real.le_sqrt_of_sq_le (by exact_mod_cast (show 1 ≤ X by omega))
  have hsmall' := (div_le_iff₀ hsqrt).mp hsmall.le
  have hscaled := mul_le_mul_of_nonneg_right hsmall' hsqrt.le
  have hsquare : (Real.sqrt (X : ℝ)) ^ 2 = X := Real.sq_sqrt hXR.le
  let z : ℝ := (X : ℝ) / Real.log (X : ℝ) ^ 16
  have hz : 32 * Real.sqrt (X : ℝ) ≤ z := by
    apply (le_div_iff₀ hpow).mpr
    nlinarith
  have hzTwo : 2 ≤ z := by linarith
  have hfloor : z < (longLength X : ℝ) + 1 := Nat.lt_floor_add_one z
  have hhalf : z / 2 ≤ (longLength X : ℝ) := by linarith
  have hLpos : 0 < longLength X := by
    apply Nat.floor_pos.mpr
    exact le_trans (by norm_num : (1 : ℝ) ≤ 2) hzTwo
  have hLle : longLength X ≤ X := by
    have h₁ : (longLength X : ℝ) ≤ z := Nat.floor_le (by positivity)
    have h₂ : z ≤ (X : ℝ) := (div_le_self hXR.le hpowOne)
    exact_mod_cast h₁.trans h₂
  have hlength : (X : ℝ) ≤ 2 * longLength X * Real.log (X : ℝ) ^ 16 := by
    have h := (div_le_iff₀ hpow).mp (show z ≤ 2 * longLength X by linarith)
    nlinarith
  have hlogPower : Real.log (X : ℝ) ≤ Real.log (X : ℝ) ^ 24 := by
    simpa only [pow_one] using pow_le_pow_right₀ hlogOne (by norm_num : 1 ≤ 24)
  refine ⟨hX, hLpos, hLle, hlength, by linarith, ?_⟩
  intro R hR
  have hRroot : (R : ℝ) ≤ Real.sqrt (X : ℝ) :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast hR)
  have hLR : (8 : ℝ) * R ≤ (longLength X : ℝ) := by
    nlinarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ (R : ℝ))]
  exact_mod_cast hLR

/-- One genuinely unconditional long-window conclusion, with thresholds uniform
in every starting point and every scale between R^m and C R^m. -/
theorem exists_uniform_long_average_deficit (m C : ℕ) (hm : 3 ≤ m) :
    ∃ R₀ : ℕ, 3 ≤ R₀ ∧ ∀ R : ℕ, R₀ ≤ R →
      ∀ X : ℕ, R ^ m ≤ X → X ≤ C * R ^ m →
      0 < longLength X ∧ longLength X ≤ X ∧
      ∀ n : ℕ, X ≤ n → n ≤ 2 * X →
        (∑ j ∈ Finset.Icc 1 (longLength X),
          smoothIndicator (R ^ (m - 1)) (n + j)) / longLength X ≤
          1 - 1 / (4 * ((m : ℝ) + 1)) := by
  obtain ⟨N₀, htheta⟩ := eventually_atTop.mp (theta_error_eventually_le_log_power 40)
  obtain ⟨X₀, hlength⟩ := eventually_atTop.mp eventually_longLength_properties
  let R₀ := max 3 (max N₀ (max X₀ (3 * C)))
  refine ⟨R₀, le_max_left _ _, ?_⟩
  intro R hR X hscale hupper
  have hR3 : 3 ≤ R := (le_max_left _ _).trans hR
  have hRN : N₀ ≤ R := by dsimp [R₀] at hR; omega
  have hRX : X₀ ≤ R := by dsimp [R₀] at hR; omega
  have hRC : 3 * C ≤ R := by dsimp [R₀] at hR; omega
  have hRone : 1 ≤ R := by omega
  have hRpow : R ≤ R ^ m := by
    calc
      R = R ^ 1 := by simp
      _ ≤ R ^ m := Nat.pow_le_pow_right hRone (by omega)
  have hRleX : R ≤ X := hRpow.trans hscale
  obtain ⟨hX3, hLpos, hLX, hL, hlarge, hcof⟩ := hlength X (hRX.trans hRleX)
  refine ⟨hLpos, hLX, ?_⟩
  intro n hn₁ hn₂
  have hRtwo : R ^ 2 ≤ X := (Nat.pow_le_pow_right hRone (by omega : 2 ≤ m)).trans hscale
  have hSquare : 3 * X ≤ R ^ (m - 1) * R ^ (m - 1) := by
    calc
      3 * X ≤ 3 * (C * R ^ m) := Nat.mul_le_mul_left 3 hupper
      _ = (3 * C) * R ^ m := by ring
      _ ≤ R * R ^ m := Nat.mul_le_mul_right _ hRC
      _ = R ^ (m + 1) := by rw [pow_succ]; ring
      _ ≤ R ^ ((m - 1) + (m - 1)) := Nat.pow_le_pow_right hRone (by omega)
      _ = _ := pow_add R _ _
  have hXpow : X ≤ R ^ (m + 1) := by
    calc
      X ≤ C * R ^ m := hupper
      _ ≤ R * R ^ m := Nat.mul_le_mul_right _ (by omega)
      _ = R ^ (m + 1) := by rw [pow_succ]; ring
  have hlogScale : Real.log (X : ℝ) ≤ ((m : ℝ) + 1) * Real.log (R : ℝ) := by
    have h : Real.log (X : ℝ) ≤ Real.log ((R ^ (m + 1) : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < X by omega)) (by exact_mod_cast hXpow)
    simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_one] using h
  exact smooth_long_average_deficit hm (by omega) hX3 hscale hn₁ hn₂ hLX
    (hcof R hRtwo) hSquare hlogScale hL hlarge (fun a ha => htheta a (hRN.trans ha))

end JSP1006
