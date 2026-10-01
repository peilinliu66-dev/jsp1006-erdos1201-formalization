/- Independent target check for JSP-001006 / Erdos 1201.
   This file does not add assumptions or replace any proof dependency.
   Run only against a successfully built, explicitly recorded project version. -/
import Erdos1201

open scoped Classical BigOperators

theorem audit_erdos1201_formalconjectures_statement :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ eta : EReal, 0 < eta → ∃ k : ℕ,
      (Filter.atTop : Filter ℕ).liminf
        (fun x : ℕ =>
          (((Nat.count
            (fun n : ℕ =>
              ((sSup {p : ℕ | p.Prime ∧ p ∣
                ∏ i ∈ Finset.range (k + 1), (n + i)} : ℕ) : ℝ) >
                  (n : ℝ) ^ (1 - epsilon)) x : ℝ) / (x : ℝ)) : EReal)) ≥
                    (1 - eta : EReal) := by
  exact Erdos1201.erdos_1201

theorem audit_erdos1201_original_statement :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ eta : ℝ, 0 < eta → ∃ k : ℕ,
      (Filter.atTop : Filter ℕ).liminf
        (fun x : ℕ =>
          (((Nat.count
            (fun n : ℕ =>
              ((sSup {p : ℕ | p.Prime ∧ p ∣
                ∏ i ∈ Finset.range (k + 1), (n + i)} : ℕ) : ℝ) >
                  (n : ℝ) ^ (1 - epsilon)) x : ℝ) / (x : ℝ)) : EReal)) ≥
                    (1 - eta : EReal) := by
  intro epsilon hepsilon eta heta
  exact audit_erdos1201_formalconjectures_statement epsilon hepsilon (eta : EReal)
    (EReal.coe_pos.mpr heta)

#print axioms audit_erdos1201_formalconjectures_statement
#print axioms audit_erdos1201_original_statement
#print axioms Erdos1201.erdos_1201
#print axioms Erdos1201.erdos_1201_eventually
