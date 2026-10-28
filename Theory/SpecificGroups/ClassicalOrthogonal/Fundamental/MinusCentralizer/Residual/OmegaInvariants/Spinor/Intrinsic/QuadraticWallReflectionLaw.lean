/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from Atlas/LinearAlgebra/QuadraticWallReflectionLaw.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Changes: CFSG imports and reflection APIs, Lean 4.33 public module boundaries,
and a separate IntrinsicWall namespace for the residual 1-g normalization.
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Spinor.Intrinsic.QuadraticResidualOutside
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Spinor.Intrinsic.QuadraticWallReflection

/-! # The general reflection law for Wall determinant classes

For a reflecting vector in the residual, use the proved one-dimensional
factorization. An outside vector enters the residual after reflection;
applying the first case again and using involutivity gives the same law.
-/
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace ClassicalOrthogonal.IntrinsicWall
open ClassicalOrthogonal.Quadratic
universe u
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate)
  (g : Q.IsometryEquiv Q) (a : V) (ha : Q a ≠ 0)

omit [FiniteDimensional F V] in
theorem reflectedIsometry_twice :
    reflectedIsometry Q (reflectedIsometry Q g a ha) a ha = g := by
  apply DFunLike.ext
  intro x
  exact Module.involutive_reflection (reflectionFunctional_self Q a ha) (g x)

/-- Multiplication by any anisotropic reflection multiplies the Wall class by Q(a). -/
theorem wallDeterminantClass_reflection :
    wallDeterminantClass Q hQ (reflectedIsometry Q g a ha) =
      Atlas.squareClass F (Units.mk0 (Q a) ha) * wallDeterminantClass Q hQ g := by
  classical
  by_cases hmem : a ∈ residual Q g
  · have h := wallDeterminantClass_reflection_residual Q hQ g ⟨a, hmem⟩ ha
    have hs : Atlas.squareClass F (Units.mk0 (Q a) ha) *
        Atlas.squareClass F (Units.mk0 (Q a) ha) = 1 := by
      rw [← map_mul, ← pow_two, Atlas.squareClass_square]
    change wallDeterminantClass Q hQ g =
      Atlas.squareClass F (Units.mk0 (Q a) ha) *
        wallDeterminantClass Q hQ (reflectedIsometry Q g a ha) at h
    rw [h, ← mul_assoc, hs]
    exact (one_mul (wallDeterminantClass Q hQ (reflectedIsometry Q g a ha))).symm
  · have hmem' := outside_mem_reflected_residual Q g hQ a ha hmem
    have h := wallDeterminantClass_reflection_residual Q hQ
      (reflectedIsometry Q g a ha) ⟨a, hmem'⟩ ha
    change wallDeterminantClass Q hQ (reflectedIsometry Q g a ha) =
      Atlas.squareClass F (Units.mk0 (Q a) ha) *
        wallDeterminantClass Q hQ
          (reflectedIsometry Q (reflectedIsometry Q g a ha) a ha) at h
    rw [reflectedIsometry_twice] at h
    exact h

end ClassicalOrthogonal.IntrinsicWall
