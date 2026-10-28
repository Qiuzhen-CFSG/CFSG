module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.Words
public import Theory.Mathieu.M24.Properties.Sylow3
import all Theory.Mathieu.M24.Properties.Sylow3

/-!
# Square conjugacy in the native M₂₄ Sylow three subgroup

All 27 elements of the existing Heisenberg subgroup have explicit ambient
square-conjugating words. Two shared ambient generators are checked once
against words in A and B; each conjugator is then a short word in those two
generators. The coordinate evaluator is separately checked against a small
point table. Every equation is checked by the kernel.

The intentional `import all` consumes the private coordinate evaluator without
changing the shared public API. The public theorem concerns membership in the
published subgroup, and `PrimeFusion` applies Sylow conjugacy. The source
application is the M₂₄ binary trace calculation for GM02, Classification of
2F-modules I, Proposition 5.1, manuscript p.17.
-/

public section
namespace Sporadic.Mathieu.M24OddCyclic

private def sharedPerm : Fin 2 → Equiv.Perm (Fin 24)
  | 0 =>
    { toFun := ![10, 22, 23, 16, 11, 17, 12, 14, 18, 20, 0, 4, 6, 21, 7, 19, 3, 5, 8, 15, 9, 13, 1, 2]
      invFun := ![10, 22, 23, 16, 11, 17, 12, 14, 18, 20, 0, 4, 6, 21, 7, 19, 3, 5, 8, 15, 9, 13, 1, 2]
      left_inv := by decide +kernel
      right_inv := by decide +kernel }
  | _ =>
    { toFun := ![20, 4, 5, 18, 6, 9, 1, 19, 0, 2, 21, 12, 11, 17, 15, 3, 16, 13, 10, 8, 23, 14, 22, 7]
      invFun := ![8, 6, 9, 15, 1, 2, 4, 23, 19, 5, 18, 12, 11, 17, 21, 14, 16, 13, 3, 7, 0, 10, 22, 20]
      left_inv := by decide +kernel
      right_inv := by decide +kernel }

private def sharedWord : Fin 2 → List (Fin 3)
  | 0 => [0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2]
  | _ => [1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2]

private theorem shared_word (i : Fin 2) :
    sharedPerm i = (Words.evaluate (sharedWord i)).val := by
  have h : ∀ i x, sharedPerm i x = Words.wordPoint (sharedWord i) x := by
    decide +kernel
  apply Equiv.ext
  intro x
  rw [Words.evaluate_apply]
  exact h i x

private noncomputable def shared (i : Fin 2) : M24 :=
  ⟨sharedPerm i, by exact (shared_word i).symm ▸ (Words.evaluate (sharedWord i)).property⟩

private noncomputable def letter : Fin 4 → M24
  | 0 => shared 0
  | 1 => (shared 0)⁻¹
  | 2 => shared 1
  | _ => (shared 1)⁻¹

private def letterPoint : Fin 4 → Fin 24 → Fin 24
  | 0 => ![10, 22, 23, 16, 11, 17, 12, 14, 18, 20, 0, 4, 6, 21, 7, 19, 3, 5, 8, 15, 9, 13, 1, 2]
  | 1 => ![10, 22, 23, 16, 11, 17, 12, 14, 18, 20, 0, 4, 6, 21, 7, 19, 3, 5, 8, 15, 9, 13, 1, 2]
  | 2 => ![20, 4, 5, 18, 6, 9, 1, 19, 0, 2, 21, 12, 11, 17, 15, 3, 16, 13, 10, 8, 23, 14, 22, 7]
  | _ => ![8, 6, 9, 15, 1, 2, 4, 23, 19, 5, 18, 12, 11, 17, 21, 14, 16, 13, 3, 7, 0, 10, 22, 20]

private theorem letter_apply : ∀ i x, (letter i).val x = letterPoint i x := by
  decide +kernel

private noncomputable def localEvaluate : List (Fin 4) → M24
  | [] => 1
  | i :: w => letter i * localEvaluate w

private def localPoint : List (Fin 4) → Fin 24 → Fin 24
  | [], x => x
  | i :: w, x => letterPoint i (localPoint w x)

private theorem localEvaluate_apply (w : List (Fin 4)) (x : Fin 24) :
    (localEvaluate w).val x = localPoint w x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (letter i).val ((localEvaluate w).val x) = _
    rw [letter_apply, ih]
    rfl

private def cubicWord : (Fin 3 × Fin 3 × Fin 3) → List (Fin 4)
  | (0, 0, 0) => []
  | (0, 0, 1) => [3, 0, 3, 3, 1, 3, 3, 1, 2, 0, 2, 0, 3, 3, 3]
  | (0, 0, 2) => [3, 0, 3, 3, 1, 3, 3, 1, 2, 0, 2, 0, 3, 3, 3]
  | (0, 1, 0) => [3, 3, 1, 3, 1, 2]
  | (0, 1, 1) => [3, 3, 1, 3, 1, 3, 3, 3]
  | (0, 1, 2) => [2, 0, 3, 1, 2, 0, 2, 0, 3, 3, 3]
  | (0, 2, 0) => [3, 3, 1, 3, 1, 2]
  | (0, 2, 1) => [2, 0, 3, 1, 2, 0, 2, 0, 3, 3, 3]
  | (0, 2, 2) => [3, 3, 1, 3, 1, 3, 3, 3]
  | (1, 0, 0) => [2, 0, 2, 0, 3, 3]
  | (1, 0, 1) => [1, 3, 3, 1, 2, 0, 2, 0, 3, 3, 3]
  | (1, 0, 2) => [1, 3, 3, 1, 2, 0, 2, 0, 3, 3, 3]
  | (1, 1, 0) => [1, 3, 3, 1, 3, 1, 3, 3, 3, 3, 1, 3, 3, 1, 2, 0, 2, 0, 3, 3, 3]
  | (1, 1, 1) => [2, 2, 0, 3, 3]
  | (1, 1, 2) => [3, 0, 3, 3, 1, 3, 3, 1, 2, 0, 2, 0, 3, 3, 3]
  | (1, 2, 0) => [2, 2, 0, 2, 1, 3, 3, 1, 2, 0, 2, 0, 3, 3, 3]
  | (1, 2, 1) => [1, 3, 3, 1, 3, 1, 3]
  | (1, 2, 2) => [3, 0, 2]
  | (2, 0, 0) => [2, 0, 2, 0, 3, 3]
  | (2, 0, 1) => [1, 3, 3, 1, 2, 0, 2, 0, 3, 3, 3]
  | (2, 0, 2) => [1, 3, 3, 1, 2, 0, 2, 0, 3, 3, 3]
  | (2, 1, 0) => [3, 0, 2]
  | (2, 1, 1) => [1, 3, 3, 1, 3, 1, 3]
  | (2, 1, 2) => [2, 2, 0, 2, 1, 3, 3, 1, 2, 0, 2, 0, 3, 3, 3]
  | (2, 2, 0) => [2, 2, 0, 3, 3]
  | (2, 2, 1) => [1, 3, 3, 1, 3, 1, 3, 3, 3, 3, 1, 3, 3, 1, 2, 0, 2, 0, 3, 3, 3]
  | (2, 2, 2) => [3, 0, 3, 3, 1, 3, 3, 1, 2, 0, 2, 0, 3, 3, 3]

private def point : (Fin 3 × Fin 3 × Fin 3) → Fin 24 → Fin 24
  | (0, 0, 0) => ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  | (0, 0, 1) => ![23, 1, 10, 21, 4, 3, 6, 20, 7, 14, 15, 11, 12, 16, 18, 2, 17, 13, 9, 0, 8, 5, 22, 19]
  | (0, 0, 2) => ![19, 1, 15, 5, 4, 21, 6, 8, 20, 18, 2, 11, 12, 17, 9, 10, 13, 16, 14, 23, 7, 3, 22, 0]
  | (0, 1, 0) => ![7, 1, 15, 3, 4, 5, 6, 16, 13, 14, 2, 22, 11, 19, 18, 10, 0, 23, 9, 8, 17, 21, 12, 20]
  | (0, 1, 1) => ![20, 1, 2, 21, 4, 3, 6, 17, 16, 18, 10, 22, 11, 0, 9, 15, 23, 19, 14, 7, 13, 5, 12, 8]
  | (0, 1, 2) => ![8, 1, 10, 5, 4, 21, 6, 13, 17, 9, 15, 22, 11, 23, 14, 2, 19, 0, 18, 20, 16, 3, 12, 7]
  | (0, 2, 0) => ![16, 1, 10, 3, 4, 5, 6, 0, 19, 18, 15, 12, 22, 8, 9, 2, 7, 20, 14, 13, 23, 21, 11, 17]
  | (0, 2, 1) => ![17, 1, 15, 21, 4, 3, 6, 23, 0, 9, 2, 12, 22, 7, 14, 10, 20, 8, 18, 16, 19, 5, 11, 13]
  | (0, 2, 2) => ![13, 1, 2, 5, 4, 21, 6, 19, 23, 14, 10, 12, 22, 20, 18, 15, 8, 7, 9, 17, 0, 3, 11, 16]
  | (1, 0, 0) => ![23, 4, 21, 9, 6, 18, 1, 7, 8, 15, 5, 11, 12, 17, 2, 3, 13, 16, 10, 0, 20, 14, 22, 19]
  | (1, 0, 1) => ![19, 4, 5, 14, 6, 9, 1, 20, 7, 2, 3, 11, 12, 13, 10, 21, 16, 17, 15, 23, 8, 18, 22, 0]
  | (1, 0, 2) => ![0, 4, 3, 18, 6, 14, 1, 8, 20, 10, 21, 11, 12, 16, 15, 5, 17, 13, 2, 19, 7, 9, 22, 23]
  | (1, 1, 0) => ![7, 4, 3, 9, 6, 18, 1, 13, 17, 2, 21, 22, 11, 0, 10, 5, 23, 19, 15, 8, 16, 14, 12, 20]
  | (1, 1, 1) => ![20, 4, 21, 14, 6, 9, 1, 16, 13, 10, 5, 22, 11, 23, 15, 3, 19, 0, 2, 7, 17, 18, 12, 8]
  | (1, 1, 2) => ![8, 4, 5, 18, 6, 14, 1, 17, 16, 15, 3, 22, 11, 19, 2, 21, 0, 23, 10, 20, 13, 9, 12, 7]
  | (1, 2, 0) => ![13, 4, 5, 9, 6, 18, 1, 23, 0, 10, 3, 12, 22, 8, 15, 21, 7, 20, 2, 17, 19, 14, 11, 16]
  | (1, 2, 1) => ![16, 4, 3, 14, 6, 9, 1, 19, 23, 15, 21, 12, 22, 7, 2, 5, 20, 8, 10, 13, 0, 18, 11, 17]
  | (1, 2, 2) => ![17, 4, 21, 18, 6, 14, 1, 0, 19, 2, 5, 12, 22, 20, 10, 3, 8, 7, 15, 16, 23, 9, 11, 13]
  | (2, 0, 0) => ![19, 6, 14, 15, 1, 10, 4, 7, 8, 3, 18, 11, 12, 16, 21, 9, 17, 13, 5, 23, 20, 2, 22, 0]
  | (2, 0, 1) => ![0, 6, 18, 2, 1, 15, 4, 20, 7, 21, 9, 11, 12, 17, 5, 14, 13, 16, 3, 19, 8, 10, 22, 23]
  | (2, 0, 2) => ![23, 6, 9, 10, 1, 2, 4, 8, 20, 5, 14, 11, 12, 13, 3, 18, 16, 17, 21, 0, 7, 15, 22, 19]
  | (2, 1, 0) => ![7, 6, 9, 15, 1, 10, 4, 17, 16, 21, 14, 22, 11, 23, 5, 18, 19, 0, 3, 8, 13, 2, 12, 20]
  | (2, 1, 1) => ![20, 6, 14, 2, 1, 15, 4, 13, 17, 5, 18, 22, 11, 19, 3, 9, 0, 23, 21, 7, 16, 10, 12, 8]
  | (2, 1, 2) => ![8, 6, 18, 10, 1, 2, 4, 16, 13, 3, 9, 22, 11, 0, 21, 14, 23, 19, 5, 20, 17, 15, 12, 7]
  | (2, 2, 0) => ![17, 6, 18, 15, 1, 10, 4, 19, 23, 5, 9, 12, 22, 8, 3, 14, 7, 20, 21, 16, 0, 2, 11, 13]
  | (2, 2, 1) => ![13, 6, 9, 2, 1, 15, 4, 0, 19, 3, 14, 12, 22, 7, 21, 18, 20, 8, 5, 17, 23, 10, 11, 16]
  | (2, 2, 2) => ![16, 6, 14, 10, 1, 2, 4, 23, 0, 21, 18, 12, 22, 20, 5, 9, 8, 7, 3, 13, 19, 15, 11, 17]

private theorem point_spec : ∀ (t : Fin 3 × Fin 3 × Fin 3) (x : Fin 24),
    (Sporadic.Mathieu.evaluate t).val x = point t x := by
  decide +kernel

private theorem cubic_check : ∀ (t : Fin 3 × Fin 3 × Fin 3) (x : Fin 24),
    localPoint (cubicWord t) (point t x) =
      point t (point t (localPoint (cubicWord t) x)) := by
  decide +kernel

private theorem square_conjugacy_of_points (g c : M24)
    (h : ∀ x : Fin 24, c.val (g.val x) = g.val (g.val (c.val x))) :
    IsConj g (g ^ 2) := by
  refine isConj_iff.mpr ⟨c, ?_⟩
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  exact Equiv.ext h

/-- Every element of the already certified Sylow three subgroup has square fusion. -/
theorem sylowThree_square_conjugacy (g : M24) (hg : g ∈ m24Sylow3Subgroup) :
    IsConj g (g ^ 2) := by
  obtain ⟨t, rfl⟩ := hg
  apply square_conjugacy_of_points _ (localEvaluate (cubicWord t))
  intro x
  rw [localEvaluate_apply, localEvaluate_apply, point_spec, point_spec, point_spec]
  exact cubic_check t x

end Sporadic.Mathieu.M24OddCyclic
