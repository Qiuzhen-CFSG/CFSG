module
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.Setup
public import Theory.GroupTheory.CosetWordCertificate.Schreier
import Mathlib.Tactic.FinCases

/-!
# Literal word inputs for the abstract Held M₁ enumeration

The seven uncommented relators and three M₁ generators in John Bray's ATLAS
`HeG1-P1.M` are written as signed words. Their evaluations are proved directly
from the abstract presentation and the definition of the subgroup. Conjugation
uses the source convention `x^g = g⁻¹*x*g`.

The original source and attribution are retained in `Held/Model/Source/`.
No numerical enumeration, presentation identification, or multiplier statement
is used in these proofs.
-/

namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets
open Subgroup.CosetWordCertificate
@[expose] public def relatorWord : Fin 7 → Word (Fin 2)
  | 0 => [(0, true), (0, true)]
  | 1 => [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]
  | 2 => [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)]
  | 3 => [(0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)]
  | 4 => [(0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true)]
  | 5 => [(0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true)]
  | 6 => [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)]

public theorem relatorWord_eq (i : Fin 7) :
    eval (PresentedGroup.of : Fin 2 → Presentation) (relatorWord i) =
      relationWord x y i := by
  fin_cases i <;>
    simp only [relatorWord, eval_cons, eval_nil, relationWord, x, y, Bool.false_eq_true,
      if_false, if_true, pow_succ, pow_zero, one_mul, mul_one, mul_inv_rev, inv_inv, mul_assoc]

public theorem relatorWord_eval (i : Fin 7) :
    eval (PresentedGroup.of : Fin 2 → Presentation) (relatorWord i) = 1 := by
  rw [relatorWord_eq, presentation_relations]

@[expose] public def subgroupWord : Fin 3 → Word (Fin 2)
  | 0 => [(0, true)]
  | 1 => [(1, false), (1, false), (0, true), (1, true), (1, true)]
  | 2 => [(1, true), (1, true), (0, true), (1, false), (1, false)]

public theorem subgroupWord_mem (i : Fin 3) :
    eval (PresentedGroup.of : Fin 2 → Presentation) (subgroupWord i) ∈ m1 := by
  apply Subgroup.subset_closure
  fin_cases i <;>
    simp [subgroupWord, eval_cons, x, y, pow_succ, mul_assoc, mul_inv_rev]

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets
