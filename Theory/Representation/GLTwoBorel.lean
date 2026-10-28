module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# The concrete Borel subgroup of GL₂

The Borel used for finite-field principal series consists of the invertible
matrices whose lower-left entry vanishes. This definition works over any field.
Closure under inversion follows from the lower-left entry of the inverse
identity and the nonzero top-left entry of an invertible triangular matrix.
The upper-unipotent elements are the existing `upperRightHom` matrices, not a
second matrix model. These definitions provide the common boundary for Borel
eigenlines and principal-series constituents in the ordinary-character degree
argument cited in Brauer, Desarguesian planes II, printed p. 128.
-/

open scoped MatrixGroups

namespace GLTwo

variable (F : Type*) [Field F]

@[expose] public def borelSubgroup : Subgroup (GL (Fin 2) F) where
  carrier := {matrix | matrix 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro left right hleft hright
    change left 1 0 = 0 at hleft
    change right 1 0 = 0 at hright
    change (left.val * right.val) 1 0 = 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, hleft, hright]
  inv_mem' := by
    intro matrix hmatrix
    change matrix 1 0 = 0 at hmatrix
    have hdiag : matrix 0 0 ≠ 0 := by
      intro hzero
      have hdet := matrix.det_ne_zero
      apply hdet
      simp [Matrix.det_fin_two, hmatrix, hzero]
    have hproduct := congrArg (fun element : GL (Fin 2) F => element 1 0)
      (inv_mul_cancel matrix)
    change (matrix⁻¹.val * matrix.val) 1 0 = (1 : Matrix (Fin 2) (Fin 2) F) 1 0
      at hproduct
    have hzero : matrix⁻¹ 1 0 * matrix 0 0 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, hmatrix] using hproduct
    exact (mul_eq_zero.mp hzero).resolve_right hdiag

@[simp] public theorem mem_borelSubgroup (matrix : GL (Fin 2) F) :
    matrix ∈ borelSubgroup F ↔ matrix 1 0 = 0 := Iff.rfl

@[expose] public def upperUnipotent (parameter : F) : borelSubgroup F :=
  ⟨Matrix.GeneralLinearGroup.upperRightHom parameter, by
    simp [borelSubgroup, Matrix.GeneralLinearGroup.upperRightHom]⟩

@[simp] public theorem coe_upperUnipotent (parameter : F) :
    (upperUnipotent F parameter : GL (Fin 2) F) =
      Matrix.GeneralLinearGroup.upperRightHom parameter := rfl

end GLTwo

