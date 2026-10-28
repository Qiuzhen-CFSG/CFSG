module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.ShortA2.SourceModel.Blocks

/-!
# Sparse elementary action on the short A₂ blocks

Multiplying a matrix on either side by an elementary transvection changes
one row or column. A single sandwich formula gives the full conjugation,
natural symmetric-square and dual symmetric-square coordinates; the fixed
block is unchanged. In characteristic two the elementary inverse has the
same parameter. These formulas apply to the literal 52-dimensional action
used by the short-root chart and avoid expanding dense matrix products.
Source: GLS3 §2.6.2, the short A₂ lattice in the split F₄ construction.
-/

@[expose] public noncomputable section
namespace ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart.BlockAction
open Matrix
open TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.ShortA2
variable {F : Type*} [Field F]

def row (s k : Bool) : Fin 3 := if k then if s then 0 else 1 else if s then 1 else 2
def column (s k : Bool) : Fin 3 := if k then if s then 1 else 0 else if s then 2 else 1

theorem generator_coe (s k : Bool) (t : F) :
    (modelGenerator F s k t).val = transvection (row s k) (column s k) t := by
  cases s <;> cases k <;> rfl

theorem transvection_transpose (i j : Fin 3) (t : F) :
    (transvection i j t).transpose = transvection j i t := by
  simp only [transvection, transpose_add, transpose_one, transpose_single]

/-- Sparse multiplication of two elementary matrices around an arbitrary matrix. -/
theorem sandwich (X : SourceBlocks.Mat F) (i j k l a b : Fin 3) (t : F) :
    (transvection i j t * X * transvection k l t) a b =
      X a b + (if a = i then t * X j b else 0) +
        (if b = l then t * X a k else 0) +
        (if a = i ∧ b = l then t ^ 2 * X j k else 0) := by
  by_cases ha : a = i <;> by_cases hb : b = l
  · subst a; subst b
    simp only [mul_transvection_apply_same, transvection_mul_apply_same,
      ↓reduceIte, and_self]
    ring
  · subst a
    rw [mul_transvection_apply_of_ne (i := k) (j := l) _ _ hb, transvection_mul_apply_same]
    simp only [↓reduceIte, hb, and_false, add_zero]
  · subst b
    rw [mul_transvection_apply_same, transvection_mul_apply_of_ne (i := i) (j := j) _ _ ha,
      transvection_mul_apply_of_ne (i := i) (j := j) _ _ ha]
    simp only [ha, ↓reduceIte, false_and, add_zero]
  · rw [mul_transvection_apply_of_ne (i := k) (j := l) _ _ hb, transvection_mul_apply_of_ne (i := i) (j := j) _ _ ha]
    simp only [ha, hb, ↓reduceIte, false_and, add_zero]

variable [CharP F 2]

theorem generator_inv (s k : Bool) (t : F) :
    (modelGenerator F s k t)⁻¹ = modelGenerator F s k t := by
  cases s <;> cases k <;>
    simp only [modelGenerator, Bool.false_eq_true, ↓reduceIte,
      SpecialLinearGroup.transvection_inv, CharTwo.neg_eq]

theorem action_mat (s k : Bool) (t : F) (v : SourceBlocks.Space F) (a b : Fin 3) :
    (SourceBlocks.action F (modelGenerator F s k t) v).1 a b =
      v.1 a b + (if a = row s k then t * v.1 (column s k) b else 0) +
        (if b = column s k then t * v.1 a (row s k) else 0) +
        (if a = row s k ∧ b = column s k then t ^ 2 * v.1 (column s k) (row s k) else 0) := by
  rw [SourceBlocks.action_apply, generator_inv, generator_coe]
  exact sandwich _ _ _ _ _ _ _ _

omit [CharP F 2] in
theorem action_fixed (s k : Bool) (t : F) (v : SourceBlocks.Space F) :
    (SourceBlocks.action F (modelGenerator F s k t) v).2.1 = v.2.1 := rfl

omit [CharP F 2] in
theorem action_sym (s k : Bool) (t : F) (v : SourceBlocks.Space F) (d a b : Fin 3) :
    ((SourceBlocks.action F (modelGenerator F s k t) v).2.2.1 d).val a b =
      (v.2.2.1 d).val a b +
        (if a = row s k then t * (v.2.2.1 d).val (column s k) b else 0) +
        (if b = row s k then t * (v.2.2.1 d).val a (column s k) else 0) +
        (if a = row s k ∧ b = row s k then t ^ 2 * (v.2.2.1 d).val (column s k) (column s k) else 0) := by
  rw [SourceBlocks.action_apply, SourceBlocks.congruence_apply, generator_coe,
    transvection_transpose]
  exact sandwich _ _ _ _ _ _ _ _

theorem action_dual (s k : Bool) (t : F) (v : SourceBlocks.Space F) (d a b : Fin 3) :
    ((SourceBlocks.action F (modelGenerator F s k t) v).2.2.2 d).val a b =
      (v.2.2.2 d).val a b +
        (if a = column s k then t * (v.2.2.2 d).val (row s k) b else 0) +
        (if b = column s k then t * (v.2.2.2 d).val a (row s k) else 0) +
        (if a = column s k ∧ b = column s k then t ^ 2 * (v.2.2.2 d).val (row s k) (row s k) else 0) := by
  rw [SourceBlocks.action_apply, SourceBlocks.congruence_apply, generator_inv,
    generator_coe, transvection_transpose, transvection_transpose]
  exact sandwich _ _ _ _ _ _ _ _

end ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart.BlockAction
