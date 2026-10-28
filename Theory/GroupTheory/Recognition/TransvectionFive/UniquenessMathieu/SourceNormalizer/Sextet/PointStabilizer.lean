module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet.Action

/-!
# Forty-eight marked point stabilizer transformations

Short products of the five centralizer shears give 48 distinct additive
transformations fixing the marked point. Their actual centralizer lifts
supply the lower bound for the ambient 45-point normalizer quotient.

Source: Aschbacher, *Sporadic Groups* (1994), 39.1 and 40.4, pp.213–218.
-/

public section

namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet
open UniquenessLinear.PlaneCensus (Code shear shearPerm rankOneGroup)

private def word : List (Fin 5) → Equiv.Perm Code
  | [] => 1
  | k :: w => word w * shearPerm k

private def words : Fin 48 → List (Fin 5) :=
  ![[],[0],[1],[2],[3],[4],[1,0],[2,0],[3,0],[4,0],[2,1],[3,1],[4,1],[1,2],[3,2],[4,2],[2,3],[4,3],[1,4],[2,1,0],[3,1,0],[4,1,0],[1,2,0],[3,2,0],[4,2,0],[2,3,0],[4,3,0],[1,4,0],[1,2,1],[3,2,1],[4,2,1],[2,3,1],[3,1,2],[4,1,2],[1,4,2],[1,2,1,0],[3,2,1,0],[4,2,1,0],[2,3,1,0],[3,1,2,0],[4,1,2,0],[1,4,2,0],[3,1,2,1],[4,1,2,1],[1,4,2,1],[3,1,2,1,0],[4,1,2,1,0],[1,4,2,1,0]]

/-- Forty-eight distinct marked point-centralizer transformations. -/
def pointSymmetry (i : Fin 48) : Equiv.Perm Code := word (words i)

theorem pointSymmetry_rankOne (i : Fin 48) : pointSymmetry i ∈ rankOneGroup := by
  have hw (w : List (Fin 5)) : word w ∈ rankOneGroup := by
    induction w with
    | nil => exact rankOneGroup.one_mem
    | cons k w ih => exact rankOneGroup.mul_mem ih (UniquenessLinear.PlaneCensus.shearPerm_mem k)
  exact hw (words i)

private def wordEval : List (Fin 5) → Code → Code
  | [], x => x
  | k :: w, x => wordEval w (shear k x)

private theorem word_apply (w : List (Fin 5)) (x : Code) : word w x = wordEval w x := by
  induction w generalizing x with
  | nil => rfl
  | cons k w ih =>
    change word w (shearPerm k x) = wordEval w (shear k x)
    rw [UniquenessLinear.PlaneCensus.shearPerm_apply, ih]

theorem pointSymmetry_point (i : Fin 48) : pointSymmetry i 4 = 4 := by
  have h : ∀ j : Fin 48, wordEval (words j) 4 = 4 := by decide
  exact (word_apply (words i) 4).trans (h i)

private def signature : Fin 48 → Code × Code × Code :=
  ![(1,2,32),(1,2,36),(3,2,32),(1,3,32),(5,2,32),(1,6,32),(3,2,36),(1,3,36),(5,2,36),(1,6,36),(3,1,32),(7,2,32),(3,6,32),(2,3,32),(5,3,32),(1,7,32),(5,7,32),(5,6,32),(7,6,32),(3,1,36),(7,2,36),(3,6,36),(2,3,36),(5,3,36),(1,7,36),(5,7,36),(5,6,36),(7,6,36),(2,1,32),(7,1,32),(3,5,32),(7,5,32),(6,3,32),(2,7,32),(6,7,32),(2,1,36),(7,1,36),(3,5,36),(7,5,36),(6,3,36),(2,7,36),(6,7,36),(6,1,32),(2,5,32),(6,5,32),(6,1,36),(2,5,36),(6,5,36)]

private theorem signature_eq : ∀ i : Fin 48,
    (wordEval (words i) 1, wordEval (words i) 2, wordEval (words i) 32) = signature i := by decide

private theorem signature_injective : Function.Injective signature := by
  change ∀ i j : Fin 48, signature i = signature j → i = j
  decide

theorem pointSymmetry_injective : Function.Injective pointSymmetry := by
  intro i j hij
  apply signature_injective
  rw [← signature_eq, ← signature_eq, ← word_apply, ← word_apply, ← word_apply,
    ← word_apply, ← word_apply, ← word_apply]
  change (pointSymmetry i 1, pointSymmetry i 2, pointSymmetry i 32) = _
  rw [hij]
  rfl

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet
