module

public import Theory.Representation.TwistedGelfand
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# GL₂ twisted bi-equivariant functions

The transpose anti-involution conjugated by the swap matrix exchanges the two
diagonal entries and fixes the upper unipotent subgroup pointwise. On the big
cell it is conjugation by an explicit upper unipotent matrix. On the triangular
cell a function bi-equivariant for a nontrivial additive character vanishes
unless the diagonal entries agree. Thus every such function is fixed by the
anti-involution, without a restriction on the characteristic or field size.

This is the GL₂-specific calculation in the proposed Whittaker multiplicity
argument for the degree list cited by Brauer, Desarguesian planes II, p. 128.
The final conditional assembly leaves the abstract transfer to irreducible
weight multiplicity explicit. It applies the symmetry result to the inverse
character, since the coefficients of the character-idempotent corner transform
by the inverse of the character acting on its weight space.
-/

open scoped MatrixGroups

namespace GLTwoWhittaker

variable {F : Type*} [Field F]

@[expose] public def swapTranspose (matrix : GL (Fin 2) F) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![matrix 1 1, matrix 0 1; matrix 1 0, matrix 0 0] (by
      simpa [Matrix.det_fin_two, mul_comm] using matrix.det_ne_zero)

@[simp] public theorem swapTranspose_apply (matrix : GL (Fin 2) F) :
    (swapTranspose matrix).val =
      !![matrix 1 1, matrix 0 1; matrix 1 0, matrix 0 0] := rfl

public theorem swapTranspose_involutive :
    Function.Involutive (swapTranspose (F := F)) := by
  intro matrix
  apply Matrix.GeneralLinearGroup.ext
  intro row col
  fin_cases row <;> fin_cases col <;> rfl

public theorem swapTranspose_mul (left right : GL (Fin 2) F) :
    swapTranspose (left * right) = swapTranspose right * swapTranspose left := by
  apply Matrix.GeneralLinearGroup.ext
  intro row col
  fin_cases row <;> fin_cases col <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

public theorem swapTranspose_upperRight (parameter : F) :
    swapTranspose (Matrix.GeneralLinearGroup.upperRightHom parameter) =
      Matrix.GeneralLinearGroup.upperRightHom parameter := by
  apply Matrix.GeneralLinearGroup.ext
  intro row col
  fin_cases row <;> fin_cases col <;> rfl

public theorem swapTranspose_eq_unipotent_conjugate (matrix : GL (Fin 2) F)
    (hlower : matrix 1 0 ≠ 0) :
    swapTranspose matrix =
      Matrix.GeneralLinearGroup.upperRightHom ((matrix 1 1 - matrix 0 0) / matrix 1 0) *
        matrix *
      Matrix.GeneralLinearGroup.upperRightHom (-((matrix 1 1 - matrix 0 0) / matrix 1 0)) := by
  apply Matrix.GeneralLinearGroup.ext
  intro row col
  fin_cases row <;> fin_cases col <;>
    simp [Matrix.GeneralLinearGroup.upperRightHom,
      Matrix.mul_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail,
      Fin.sum_univ_two] <;> try field_simp
  all_goals ring

private theorem triangular_unipotent_relation (matrix : GL (Fin 2) F)
    (hlower : matrix 1 0 = 0) (parameter : F) :
    Matrix.GeneralLinearGroup.upperRightHom (matrix 0 0 * parameter) * matrix =
      matrix * Matrix.GeneralLinearGroup.upperRightHom (matrix 1 1 * parameter) := by
  apply Matrix.GeneralLinearGroup.ext
  intro row col
  fin_cases row <;> fin_cases col <;>
    simp [Matrix.GeneralLinearGroup.upperRightHom,
      Matrix.mul_apply, Fin.sum_univ_two, hlower]
  ring

private theorem triangular_vanish (psi : AddChar F ℂ) (hpsi : psi ≠ 1)
    (function : GL (Fin 2) F → ℂ)
    (hfunction : ∀ (left right : F) (matrix : GL (Fin 2) F),
      function (Matrix.GeneralLinearGroup.upperRightHom left * matrix *
        Matrix.GeneralLinearGroup.upperRightHom right) =
      psi left * function matrix * psi right)
    (matrix : GL (Fin 2) F) (hlower : matrix 1 0 = 0)
    (hdiagonal : matrix 0 0 ≠ matrix 1 1) : function matrix = 0 := by
  by_contra hnonzero
  have hequal (parameter : F) :
      psi (matrix 0 0 * parameter) = psi (matrix 1 1 * parameter) := by
    have hleft := hfunction (matrix 0 0 * parameter) 0 matrix
    have hright := hfunction 0 (matrix 1 1 * parameter) matrix
    simp only [AddChar.map_zero_eq_one, mul_one, one_mul] at hleft hright
    rw [triangular_unipotent_relation matrix hlower parameter] at hleft
    exact mul_right_cancel₀ hnonzero (hleft.symm.trans (hright.trans (mul_comm _ _)))
  apply hpsi
  ext parameter
  have hdifference : matrix 0 0 - matrix 1 1 ≠ 0 := sub_ne_zero.mpr hdiagonal
  have heq := hequal (parameter / (matrix 0 0 - matrix 1 1))
  have hsplit : parameter = matrix 0 0 * (parameter / (matrix 0 0 - matrix 1 1)) -
      matrix 1 1 * (parameter / (matrix 0 0 - matrix 1 1)) := by
    field_simp
  rw [AddChar.one_apply, hsplit, psi.map_sub_eq_div, heq]
  exact div_self (psi.val_isUnit _).ne_zero

public theorem biEquivariant_swapTranspose (psi : AddChar F ℂ) (hpsi : psi ≠ 1)
    (function : GL (Fin 2) F → ℂ)
    (hfunction : ∀ (left right : F) (matrix : GL (Fin 2) F),
      function (Matrix.GeneralLinearGroup.upperRightHom left * matrix *
        Matrix.GeneralLinearGroup.upperRightHom right) =
      psi left * function matrix * psi right)
    (matrix : GL (Fin 2) F) : function (swapTranspose matrix) = function matrix := by
  by_cases hlower : matrix 1 0 = 0
  · by_cases hdiagonal : matrix 0 0 = matrix 1 1
    · congr 1
      apply Matrix.GeneralLinearGroup.ext
      intro row col
      fin_cases row <;> fin_cases col <;> simp [hdiagonal]
    · rw [triangular_vanish psi hpsi function hfunction matrix hlower hdiagonal]
      apply triangular_vanish psi hpsi function hfunction
      · exact hlower
      · exact Ne.symm hdiagonal
  · rw [swapTranspose_eq_unipotent_conjugate matrix hlower, hfunction]
    rw [mul_right_comm, ← psi.map_add_eq_mul, add_neg_cancel,
      psi.map_zero_eq_one, one_mul]

end GLTwoWhittaker

public theorem gl2_nontrivial_unipotent_weight_finrank_le_one
    {F : Type*} [Field F] [Finite F]
    (size : ℕ) (rho : Representation ℂ (GL (Fin 2) F) (Fin size → ℂ))
    (hirred : Representation.IsIrreducible rho) (psi : AddChar F ℂ) (hpsi : psi ≠ 1) :
    Module.finrank ℂ
      (⨅ parameter : F,
        Module.End.eigenspace
          (rho (Matrix.GeneralLinearGroup.upperRightHom parameter)) (psi parameter) :
        Submodule ℂ (Fin size → ℂ)) ≤ 1 := by
  apply Representation.weight_finrank_le_one_of_twisted_gelfand rho hirred
    (Matrix.GeneralLinearGroup.upperRightHom : AddChar F (GL (Fin 2) F)) psi
    GLTwoWhittaker.swapTranspose
    GLTwoWhittaker.swapTranspose_involutive GLTwoWhittaker.swapTranspose_mul
    GLTwoWhittaker.swapTranspose_upperRight
  intro function hfunction matrix
  apply GLTwoWhittaker.biEquivariant_swapTranspose psi⁻¹
    (inv_ne_one.mpr hpsi) function
  simpa only [AddChar.inv_apply'] using hfunction

#print axioms gl2_nontrivial_unipotent_weight_finrank_le_one
