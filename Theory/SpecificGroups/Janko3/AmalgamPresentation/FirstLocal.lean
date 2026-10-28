module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Core
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.LocalBound
import Mathlib.Tactic.FinCases

/-!
# The literal first local subgroup of the universal amalgam

Its six relations are the first six of the universal relation list. The checked
local presentation therefore bounds this exact subgroup by 8160.
-/

public section
namespace Sporadic.Janko3.AmalgamPresentation
open Subgroup Subgroup.CosetWordCertificate

/-- Restricting the exact six-generator marking gives the first local relations. -/
theorem satisfies_firstLocal {G : Type*} [Group G] {g : Fin 6 → G}
    (h : Satisfies g) : LocalBound.Satisfies (g 0) (g 1) := by
  intro i
  have hi := h ⟨i.val, lt_trans i.isLt (by decide)⟩
  fin_cases i <;>
    simpa [relatorWord, LocalBound.relator, eval_cons, pow_succ, mul_assoc] using hi

/-- Finiteness and the order bound apply to the literal first local subgroup. -/
theorem firstLocal_finite_card : Finite firstLocal ∧ Nat.card firstLocal ≤ 8160 :=
  LocalBound.closure_finite_card (satisfies_firstLocal generator_satisfies)

end Sporadic.Janko3.AmalgamPresentation
