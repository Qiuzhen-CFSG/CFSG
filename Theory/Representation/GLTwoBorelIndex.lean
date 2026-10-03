module

public import Theory.Representation.GLTwoBorel
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Index of the concrete GL₂ Borel

Over any finite field F of cardinality q, the upper-triangular subgroup
`GLTwo.borelSubgroup F` has index q + 1. No restriction on the characteristic
is needed, so the result includes the field with two elements.

An invertible triangular matrix has two nonzero diagonal entries. Recording
these as units, together with the arbitrary upper-right entry, gives a
bijection with `(Fˣ × Fˣ) × F`, hence Borel order (q − 1)²q. Mathlib's
`Matrix.card_GL_field` gives ambient order (q² − 1)(q² − q). Factoring this
expression and cancelling the positive Borel order in Lagrange's identity
proves the index formula.

This elementary counting result supplies the dimension input for finite-field
principal series, used in the ordinary-character degree argument cited in
Brauer, Desarguesian planes II, printed p. 128. It uses the shared concrete
Borel without introducing a second subgroup model.
-/

open scoped MatrixGroups

namespace GLTwo

variable {F : Type*} [Field F]

private theorem diagonal_ne_zero (matrix : borelSubgroup F) :
    matrix.val 0 0 ≠ 0 ∧ matrix.val 1 1 ≠ 0 := by
  have hdet := matrix.val.det_ne_zero
  have hlower := (mem_borelSubgroup F matrix.val).mp matrix.property
  simpa [Matrix.det_fin_two, hlower, mul_ne_zero_iff] using hdet

private def borelCoordinates : borelSubgroup F ≃ (Fˣ × Fˣ) × F where
  toFun matrix :=
    ((Units.mk0 (matrix.val 0 0) (diagonal_ne_zero matrix).1,
      Units.mk0 (matrix.val 1 1) (diagonal_ne_zero matrix).2), matrix.val 0 1)
  invFun entries :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![(entries.1.1 : F), entries.2; 0, (entries.1.2 : F)]
      (by simp [Matrix.det_fin_two]), by simp⟩
  left_inv matrix := by
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro row column
    fin_cases row <;> fin_cases column <;>
      simp [(mem_borelSubgroup F matrix.val).mp matrix.property]
  right_inv entries := by
    rcases entries with ⟨⟨first, second⟩, upper⟩
    apply Prod.ext
    · apply Prod.ext <;> apply Units.ext <;> rfl
    · rfl

private theorem borel_card [Finite F] :
    Nat.card (borelSubgroup F) = (Nat.card F - 1) ^ 2 * Nat.card F := by
  rw [Nat.card_congr borelCoordinates]
  simp [Nat.card_prod, Nat.card_units, pow_two]

public theorem borelSubgroup_index [Finite F] :
    (borelSubgroup F).index = Nat.card F + 1 := by
  let := Fintype.ofFinite F
  have hcard := (borelSubgroup F).index_mul_card
  rw [borel_card, Matrix.card_GL_field] at hcard
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    ← Nat.card_eq_fintype_card] at hcard
  have hpos : 0 < Nat.card (borelSubgroup F) := Nat.card_pos
  rw [borel_card] at hpos
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [hcard]
  have hfirst : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
    rw [pow_two, mul_self_tsub_one, mul_comm]
  have hsecond : Nat.card F ^ 2 - Nat.card F = Nat.card F * (Nat.card F - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one, pow_two]
  rw [hfirst, hsecond]
  ring

end GLTwo
