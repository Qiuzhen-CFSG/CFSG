/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from Atlas/LinearAlgebra/BilinearDeterminantClass.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Changes: CFSG imports and reflection APIs, Lean 4.33 public module boundaries,
and the existing shared Atlas.SquareClass quotient (where needed).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Spinor.SquareClasses
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! # The determinant square class of a nondegenerate bilinear form

A change of basis multiplies the Gram determinant by the square of the
transition determinant. Thus every nondegenerate bilinear form has a
well-defined determinant in the shared field square classes.
-/
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace Atlas.Bilinear
variable {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
  [Fintype ι] [DecidableEq ι]
variable (B : LinearMap.BilinForm F V) (hB : B.Nondegenerate)

def gramUnit (b : Module.Basis ι F V) : Fˣ :=
  Units.mk0 (LinearMap.BilinForm.toMatrix b B).det
    ((LinearMap.nondegenerate_iff_det_ne_zero b).mp hB)

def determinantClass (b : Module.Basis ι F V) : Atlas.SquareClass F :=
  Atlas.squareClass F (gramUnit B hB b)

/-- Changing a basis multiplies the Gram determinant by a square unit. -/
theorem gramUnit_basis_change (b c : Module.Basis ι F V) :
    ∃ a : Fˣ, gramUnit B hB c = gramUnit B hB b * a^2 := by
  have hi := congrArg Matrix.det (b.toMatrix_mul_toMatrix_flip c)
  simp only [Matrix.det_mul, Matrix.det_one] at hi
  have hn : (b.toMatrix c).det ≠ 0 := by
    intro h
    rw [h, zero_mul] at hi
    exact zero_ne_one hi
  refine ⟨Units.mk0 (b.toMatrix c).det hn, ?_⟩
  have hm := congrArg Matrix.det (LinearMap.BilinForm.toMatrix_mul_basis_toMatrix b c B)
  simp only [Matrix.det_mul, Matrix.det_transpose] at hm
  apply Units.ext
  change (LinearMap.BilinForm.toMatrix c B).det =
    (LinearMap.BilinForm.toMatrix b B).det * (b.toMatrix c).det^2
  rw [← hm]
  ring

/-- The determinant square class does not depend on the chosen ordered basis. -/
theorem determinantClass_basis_independent (b c : Module.Basis ι F V) :
    determinantClass B hB b = determinantClass B hB c := by
  obtain ⟨a, ha⟩ := gramUnit_basis_change B hB b c
  change Atlas.squareClass F (gramUnit B hB b) = Atlas.squareClass F (gramUnit B hB c)
  rw [ha, Atlas.squareClass_mul_square]

end Atlas.Bilinear
