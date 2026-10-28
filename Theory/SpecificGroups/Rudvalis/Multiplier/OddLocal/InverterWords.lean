module

public import Theory.SpecificGroups.Rudvalis.Model.OrderCheck
public import Mathlib.Tactic.FinCases

/-!
# Standard words for Rudvalis odd-local inverters

The original ATLAS letters a,b and their inverses retain the existing left
permutation convention. This connects the checked inverter words to the
actual model. Source and attribution: `Model.PermutationData`.
-/

namespace Rudvalis.Multiplier.OddLocal
open Theory.GroupTheory

@[expose] public def atlasGen : Fin 4 → Model := ![a, b, a⁻¹, b⁻¹]
@[expose] public def atlasPerm : Fin 4 → Equiv.Perm (Fin 4060) :=
  ![aPerm, bPerm, aPerm⁻¹, bPerm⁻¹]

private theorem atlasPerm_eq (i : Fin 4) :
    atlasPerm i = modelSubgroup.subtype (atlasGen i) := by
  fin_cases i <;> rfl

public theorem word_eq (w : List (Fin 4)) :
    evalWord atlasPerm w = modelSubgroup.subtype (evalWord atlasGen w) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [evalWord, atlasPerm_eq, ih]; rfl

end Rudvalis.Multiplier.OddLocal
