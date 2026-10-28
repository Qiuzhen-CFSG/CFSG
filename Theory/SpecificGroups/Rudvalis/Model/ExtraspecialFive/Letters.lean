module
public import Theory.SpecificGroups.Rudvalis.Model.Basic
public import Theory.GroupTheory.WordSubgroup
import Mathlib.Tactic.FinCases

/-!
# The original ATLAS letters for the Rudvalis five-local certificates

The four letters are the two actual degree-4060 generators and their inverses.
Evaluation in cached permutations agrees with evaluation in the literal model.
The descendants certify short consecutive segments of retained generator words.

Source: Wilson–Nickerson–Bray, ATLAS of Finite Group Representations,
RuG1-p4060B0; the original files and inverse-action convention remain in
`Model.PermutationData`. See `source/README.md` for the discovery data.
-/

namespace Rudvalis.ExtraspecialFive
open Theory.GroupTheory

@[expose] public def letter : Fin 4 → Model
  | 0 => a
  | 1 => b
  | 2 => a⁻¹
  | 3 => b⁻¹

@[expose] public def permutationLetter : Fin 4 → Equiv.Perm (Fin 4060)
  | 0 => aPerm
  | 1 => bPerm
  | 2 => aPerm⁻¹
  | 3 => bPerm⁻¹

private theorem permutationLetter_eq (i : Fin 4) :
    permutationLetter i = modelSubgroup.subtype (letter i) := by
  fin_cases i <;> rfl

public theorem word_eq (w : List (Fin 4)) :
    evalWord permutationLetter w = modelSubgroup.subtype (evalWord letter w) := by
  induction w with
  | nil => exact (map_one modelSubgroup.subtype).symm
  | cons i w ih =>
    simp only [evalWord, permutationLetter_eq, ih]
    rfl

end Rudvalis.ExtraspecialFive
