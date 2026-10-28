/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from Atlas/LinearAlgebra/QuadraticWallReflection.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Changes: CFSG imports and reflection APIs, Lean 4.33 public module boundaries,
and a separate IntrinsicWall namespace for the residual 1-g normalization.
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Spinor.Intrinsic.QuadraticResidualReflection
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Spinor.Intrinsic.QuadraticWallDeterminant
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Spinor.Intrinsic.BilinearDeterminantTransport

/-! # Wall determinant factorization for anisotropic residual reflections

Split the original residual at its anisotropic reflecting vector. The
reflected residual is isometric to the right-perpendicular factor, so the
triangular Gram determinant contributes exactly the square class of `Q(u)`.
-/
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace ClassicalOrthogonal.IntrinsicWall
open ClassicalOrthogonal.Quadratic
universe u
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate)
  (g : Q.IsometryEquiv Q) (u : residual Q g) (hu : Q u.val ≠ 0)

/-- Reflection at an anisotropic residual vector removes its quadratic square class. -/
theorem wallDeterminantClass_reflection_residual :
    wallDeterminantClass Q hQ g = Atlas.squareClass F (Units.mk0 (Q u.val) hu) *
      wallDeterminantClass Q hQ (reflectedIsometry Q g u.val hu) := by
  classical
  let h := reflectedIsometry Q g u.val hu
  let E := reflectedResidualEquiv Q g u hu
  let b := Module.finBasis F (residual Q h)
  let c := b.map E
  have hu' : wallForm Q g u u ≠ 0 := (wallForm_self Q g u) ▸ hu
  have hc := Atlas.Bilinear.linePerpForm_nondegenerate (wallForm Q g) u hu' c
    (wallForm_nondegenerate Q g hQ)
  have ht := Atlas.Bilinear.determinantClass_transport (wallForm Q h)
    (wallForm_nondegenerate Q h hQ) (Atlas.Bilinear.linePerpForm (wallForm Q g) u)
    hc E (fun x y => (reflected_wallForm Q g u hu x y).symm) b
  unfold wallDeterminantClass
  rw [Atlas.Bilinear.determinantClass_basis_independent_any (wallForm Q g)
    (wallForm_nondegenerate Q g hQ) (Module.finBasis F (residual Q g))
    (Atlas.Bilinear.lineBasis (wallForm Q g) u hu' c)]
  rw [Atlas.Bilinear.determinantClass_line]
  have hs : Units.mk0 (wallForm Q g u u) hu' = Units.mk0 (Q u.val) hu :=
    Units.ext (wallForm_self Q g u)
  rw [hs]
  exact congrArg (fun t => Atlas.squareClass F (Units.mk0 (Q u.val) hu) * t) ht

end ClassicalOrthogonal.IntrinsicWall
