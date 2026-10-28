module

public import Theory.SpecificGroups.Held.Model.FourPointBase
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.Evaluator
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.Data

import Mathlib.Tactic.FinCases

/-!
# The seventh marked word in the concrete Held carrier

Evaluate the literal marked word on the certified four-point base of Held.
The packed evaluator agrees with the retained ATLAS permutations, and the
four-point base theorem turns these four checked values into group equality.
This places the mapped seventh word in the covering kernel; it makes no
claim that the word vanishes in the abstract source presentation.

Source: John Bray's ATLAS `Held/Model/Source/HeG1-P1.M`, the retained
`HeG1-p2058B0` permutations, and `M1Restriction/Data.lean`.
-/

public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd
open Subgroup.CosetWordCertificate
open Held.Realization.MarkedConjugacy.NormalizedPairs.ClassA

private def fastGen (i : Fin 3) (p : Nat) : Nat :=
  match i with
  | 0 => fastA p
  | 1 => fastBi (fastBi (fastA (fastB (fastB p))))
  | 2 => fastB (fastB (fastA (fastBi (fastBi p))))

private theorem fastGen_correct (i : Fin 3) (p : Fin 2058) :
    fastGen i p.val = (representation (concreteGenerator i) p).val := by
  fin_cases i <;>
    simp only [fastGen, concreteGenerator_eq, map_mul, map_inv,
      representation, a, b, Subgroup.subtype_apply, Equiv.Perm.mul_apply, pow_two,
      mul_inv_rev]
  all_goals
    simp only [(fast_correct _).1, (fast_correct _).2.1, (fast_correct _).2.2]

private def fastWord : List (Fin 3) → Nat → Nat
  | [], p => p
  | i :: w, p => fastGen i (fastWord w p)

private theorem fastWord_correct (w : List (Fin 3)) (p : Fin 2058) :
    fastWord w p.val =
      (representation (presentationMap (eval liftedGenerator (w.map (fun i => (i,true))))) p).val := by
  induction w with
  | nil => simp [fastWord]
  | cons i w ih =>
    simp only [fastWord, List.map_cons, eval_cons, ↓reduceIte, map_mul,
      Equiv.Perm.mul_apply, ih, fastGen_correct, concreteGenerator]

private theorem check7 : ∀ i : Fin 4, fastWord (relationIndices 7) i.val = i.val := by
  decide +kernel

set_option maxRecDepth 2048 in
theorem seventh_model : presentationMap (eval liftedGenerator (relationLetters 7)) = 1 := by
  apply Held.eq_of_four_point_images
  intro i
  apply Fin.ext
  exact (fastWord_correct (relationIndices 7) ⟨i.val, by omega⟩).symm.trans (check7 i)
end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd
