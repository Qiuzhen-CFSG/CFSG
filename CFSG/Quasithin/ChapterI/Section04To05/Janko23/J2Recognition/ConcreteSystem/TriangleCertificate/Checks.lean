module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.ConcreteSystem.TriangleCertificate.Data

/-!
# Kernel checks for the J₂ triangle reduction

Neighbor rows transport by one generator step along the existing word tree.
Induction gives the full word action without repeated long-word evaluation.
The remaining checks certify the spanning tree and strictly smaller ranks of
both replacement edges. All finite equalities are checked by Lean's kernel.

Source: the cycle-base argument of Aschbacher, *Sporadic Groups*, §§34–37.
-/

public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.TriangleCertificate
open OrbitAction OrbitAction.Data GeneratorPair FirstFusion
private theorem checkedAt {n : Nat} {f : Fin n → Bool}
    (h : checkFin f = true) (i : Fin n) : f i = true := by
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt] using hi

private theorem neighbor_zero_check : ∀ k : Fin 36, neighborIndex 0 k = neighborRow k := by
  decide +kernel

private theorem neighbor_step_check (i : Fin 280) (hi : i ≠ 0) (k : Fin 36) :
    nextRow (neighborIndex i k) (invLetter (OrbitAction.Data.parentLetter i)) =
      neighborIndex (OrbitAction.Data.parent i) k := by
  have h : checkFin (fun i : Fin 280 => checkFin (fun k : Fin 36 => decide
    (i ≠ 0 → nextRow (neighborIndex i k) (invLetter (OrbitAction.Data.parentLetter i)) =
      neighborIndex (OrbitAction.Data.parent i) k))) = true := by decide +kernel
  exact of_decide_eq_true (checkedAt (checkedAt h i) k) hi

private theorem actWord_append (u v : List (Fin 3)) (i : Fin 280) :
    actWord (u ++ v) i = actWord u (actWord v i) := by
  induction u with
  | nil => rfl
  | cons s u ih => simp only [List.cons_append, actWord, ih]

/-- Full word transport follows from single generator steps along the checked word tree. -/
theorem neighbor_spec (i : Fin 280) (k : Fin 36) :
    actWord (words i) (neighborIndex i k) = neighborRow k := by
  have aux : ∀ (n : Nat) (j : Fin 280), j.val = n →
      actWord (words j) (neighborIndex j k) = neighborRow k := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj
      by_cases hz : j = 0
      · subst j
        exact neighbor_zero_check k
      obtain ⟨hlt, hw, _, _⟩ := word_data j hz
      rw [hw, actWord_append]
      change actWord (words (OrbitAction.Data.parent j))
        (nextRow (neighborIndex j k) (invLetter (OrbitAction.Data.parentLetter j))) = _
      rw [neighbor_step_check j hz k]
      exact ih _ (hj ▸ hlt) _ rfl
  exact aux _ i rfl

theorem tree_data (i : Fin 280) : parent (parent i) = 0 ∧
    (i ≠ 0 → neighborIndex (parent i) (treeIndex i) = i) ∧
    (parent i ≠ 0 → neighborIndex 0 (rootIndex i) = parent i) := by
  have h : checkFin (fun i : Fin 280 => decide (parent (parent i) = 0 ∧
      (i ≠ 0 → neighborIndex (parent i) (treeIndex i) = i) ∧
      (parent i ≠ 0 → neighborIndex 0 (rootIndex i) = parent i))) = true := by decide +kernel
  exact of_decide_eq_true (checkedAt h i)

theorem reduction_data (i : Fin 280) (k : Fin 36) :
    (rank i (neighborIndex i k) = 0 → parent i = neighborIndex i k ∨ parent (neighborIndex i k) = i) ∧
    (rank i (neighborIndex i k) ≠ 0 →
      neighborIndex i (leftIndex i k) = pivot i (neighborIndex i k) ∧
      neighborIndex (pivot i (neighborIndex i k)) (rightIndex i k) = neighborIndex i k ∧
      rank i (pivot i (neighborIndex i k)) < rank i (neighborIndex i k) ∧
      rank (pivot i (neighborIndex i k)) (neighborIndex i k) < rank i (neighborIndex i k)) := by
  have h : checkFin (fun i : Fin 280 => checkFin (fun k : Fin 36 => decide (
    (rank i (neighborIndex i k) = 0 → parent i = neighborIndex i k ∨ parent (neighborIndex i k) = i) ∧
    (rank i (neighborIndex i k) ≠ 0 →
      neighborIndex i (leftIndex i k) = pivot i (neighborIndex i k) ∧
      neighborIndex (pivot i (neighborIndex i k)) (rightIndex i k) = neighborIndex i k ∧
      rank i (pivot i (neighborIndex i k)) < rank i (neighborIndex i k) ∧
      rank (pivot i (neighborIndex i k)) (neighborIndex i k) < rank i (neighborIndex i k))))) = true := by
    decide +kernel
  exact of_decide_eq_true (checkedAt (checkedAt h i) k)
end Sporadic.LeechRelated.J2.RecognitionGeometry.TriangleCertificate
