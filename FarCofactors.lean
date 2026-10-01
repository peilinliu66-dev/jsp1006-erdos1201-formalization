/-
Localized cofactor cancellation for JSP1006. UNCOMPILED DRAFT.
The finite distance hypothesis below is proved eventually for real coefficients
in RealFarSeparation; it is not the final short-interval theorem as an assumption.
-/
import RealFarSeparation
import ErdosProblems.Erdos67b.MRCofactorComplementaryPrefixes

open scoped Classical

open Filter
open scoped BigOperators ComplexConjugate
open Erdos67b Erdos67b.MRHalaszBands

namespace JSP1006

noncomputable section

def FarNonpretentious (f : ℕ → ℂ) (M X : ℕ) : Prop :=
  ∀ t : ℝ, 1 ≤ |t| → |t| ≤ (X : ℝ) →
    (M : ℝ) ≤ pretentiousDistSq f (archimedeanTwist t) X

theorem eventually_farNonpretentious (M : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ f : ℕ → ℂ,
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, 0 < n → ‖f n‖ ≤ 1) → FarNonpretentious f M X := by
  simpa only [FarNonpretentious] using eventually_real_far_twist_distance (M : ℝ)

/-- Deleting prime bands and lowering the endpoint only cost the already proved
finite distance loss. The whole local frequency window stays away from zero. -/
theorem deletedUntwist_localDistance_of_far
    {f : ℕ → ℂ} (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (Q : ℕ → Prop) [DecidablePred Q] {N M Z X : ℕ}
    (hNM : 2 * (N : ℝ) + mrCofactorDistanceLoss ≤ M)
    (hZ : 2 ≤ Z) (hZX : Z ≤ X)
    (hlog : Real.log (X : ℝ) ≤ 2 * Real.log (Z : ℝ))
    {t : ℝ} (haway : 1 + Real.log (X : ℝ) ^ 2 ≤ |t|)
    (hwindow : |t| + Real.log (X : ℝ) ^ 2 ≤ X)
    (hfar : FarNonpretentious f M X) :
    ∀ u : ℝ, |u| ≤ Real.log (Z : ℝ) ^ 2 →
      (N : ℝ) ≤ pretentiousDistSq
        (gsDeletePrimeBand (archimedeanUntwist f t) Q) (archimedeanTwist u) Z := by
  intro u hu
  have hlogZ : 0 ≤ Real.log (Z : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ Z by omega))
  have hlogZX : Real.log (Z : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < Z by omega)) (by exact_mod_cast hZX)
  have hheight := pow_le_pow_left₀ hlogZ hlogZX 2
  have hfreqUpper : |t + u| ≤ (X : ℝ) :=
    (abs_add_le t u).trans (by linarith)
  have htriangle : |t| ≤ |t + u| + |u| := by
    calc
      |t| = |(t + u) - u| := by congr 1; ring
      _ ≤ |t + u| + |u| := abs_sub _ _
  have hfreqLower : 1 ≤ |t + u| := by linarith
  have hdist := hfar (t + u) hfreqLower hfreqUpper
  have hloss := mrPretentiousDistSq_tail_le_cofactorLoss hZ hZX hlog
    (fun p hp => hf p hp.pos)
    (fun p hp => (norm_archimedeanTwist hp.pos (t + u)).le)
  have hdelete := half_pretentiousDistSq_le_deletePrimeBand
    (f := archimedeanUntwist f t) (g := archimedeanTwist u)
    (fun p hp => by rw [mrNorm_archimedeanUntwist_of_pos f t hp.pos]; exact hf p hp.pos)
    (fun p hp => (norm_archimedeanTwist hp.pos u).le) Q Z
  rw [mrPretentiousDistSq_archimedeanUntwist] at hdelete
  linarith

/-- The source's proved local-distance cofactor estimate applies on the far set.
All constants precede the ambient scale and the coefficient f. -/
theorem exists_far_complementary_typical_prefixes
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ ∃ M₀ Y₀ : ℕ, 0 < M₀ ∧ 2 ≤ Y₀ ∧
      ∀ {M X Y : ℕ}, M₀ ≤ M → Y₀ ≤ Y → Y ≤ X →
        Real.log (X : ℝ) ≤ 2 * Real.log (Y : ℝ) →
      ∀ (Q : ℕ → Prop) [DecidablePred Q],
      ∀ (J : Finset ℕ) (B : ℕ → Finset ℕ),
        (∀ j ∈ J, 1 ≤ j) → (∀ j ∈ J, B j ⊆ primesUpTo Y) →
        Set.PairwiseDisjoint (↑J : Set ℕ) B →
        (∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (Y : ℝ) / 16) →
        (∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ)) →
        (∀ j ∈ J, ∀ p ∈ B j, p ≤ mrCofactorPowerCutoff delta Y) →
        (∀ j ∈ J, ∀ p ∈ B j, 23 ≤ p) →
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → FarNonpretentious f M X →
      ∀ t : ℝ, 1 + Real.log (X : ℝ) ^ 2 ≤ |t| →
        |t| + Real.log (X : ℝ) ^ 2 ≤ X → ∀ Z ∈ Finset.Icc Y X,
        ‖positivePrefixSum (mrIndexedTypicalCoefficient J B
          (gsDeletePrimeBand (archimedeanUntwist f t) Q)) Z‖ / (Z : ℝ) ≤ epsilon := by
  obtain ⟨delta, hd0, hd1, N₀, Z₀, hN₀, hmean⟩ :=
    mrExists_uniform_small_mean_restoredTypicalCofactor_of_localDistance hepsilon
  let M₀ := 2 * N₀ + ⌈mrCofactorDistanceLoss⌉₊
  refine ⟨delta, hd0, hd1, M₀, max Z₀ 2, by dsimp [M₀]; omega,
    le_max_right _ _, ?_⟩
  intro M X Y hM hY hYX hlogXY Q _ J B hJ hB hdisj hsmall hmass hBy hlarge
    f hmul hbound hfar t haway hwindow Z hZ
  obtain ⟨hYZ, hZX⟩ := Finset.mem_Icc.mp hZ
  have hYtwo : 2 ≤ Y := (le_max_right _ _).trans hY
  have hZtwo : 2 ≤ Z := hYtwo.trans hYZ
  have hlogYZ : Real.log (Y : ℝ) ≤ Real.log (Z : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < Y by omega)) (by exact_mod_cast hYZ)
  have hNM : 2 * (N₀ : ℝ) + mrCofactorDistanceLoss ≤ M := by
    have hceil := Nat.le_ceil mrCofactorDistanceLoss
    have hcast : 2 * (N₀ : ℝ) + (⌈mrCofactorDistanceLoss⌉₊ : ℝ) ≤ M := by
      exact_mod_cast hM
    linarith
  have hcutoff := mrCofactorPowerCutoff_mono hd0.le (show 0 < Y by omega) hYZ
  have hg := gsDeletePrimeBand_isMultiplicativeOnPositiveNat
    (archimedeanUntwist_isMultiplicative hmul t) Q
  have hgbound : ∀ n, 0 < n →
      ‖gsDeletePrimeBand (archimedeanUntwist f t) Q n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one
      (fun m hm => by rw [mrNorm_archimedeanUntwist_of_pos f t hm]; exact hbound m hm) Q hn
  have hlocal := deletedUntwist_localDistance_of_far hbound Q hNM hZtwo hZX
    (by linarith) haway hwindow hfar
  have hresult := hmean (N := N₀) (X := Z) le_rfl
    (((le_max_left Z₀ 2).trans hY).trans hYZ) ∅ (by simp) J B hJ
    (fun j hj => (hB j hj).trans (primesUpTo_mono hYZ)) hdisj
    (fun j hj p hp => (hsmall j hj p hp).trans
      (div_le_div_of_nonneg_right hlogYZ (by norm_num))) hmass (by simp)
    (fun j hj p hp => (hBy j hj p hp).trans hcutoff) hlarge hg hgbound hlocal
  simpa only [mrIndexedTypicalCofactorCoefficient_empty] using hresult

end

end JSP1006
