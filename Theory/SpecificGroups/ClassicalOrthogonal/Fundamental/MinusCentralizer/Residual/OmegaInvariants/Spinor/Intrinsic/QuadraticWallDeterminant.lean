/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from Atlas/LinearAlgebra/QuadraticWallDeterminant.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Changes: CFSG imports and reflection APIs, Lean 4.33 public module boundaries,
and a separate IntrinsicWall namespace for the residual 1-g normalization.
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Spinor.Intrinsic.QuadraticResidual
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Spinor.Intrinsic.BilinearDeterminantClass

/-! # The intrinsic determinant class of Wall's residual pairing

This file defines the determinant-class function. Multiplicativity is a separate
obligation; no spinor-norm homomorphism is asserted here.

The nondegenerate residual pairing has a nonzero Gram determinant. Passing
to the shared field square classes removes the choice of basis; the later
reflection law proves that this invariant is multiplicative.
-/
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace ClassicalOrthogonal.IntrinsicWall
open ClassicalOrthogonal.Quadratic
universe u
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (hQ : Q.polarBilin.Nondegenerate)

def wallDeterminantClass (g : Q.IsometryEquiv Q) : Atlas.SquareClass F :=
  Atlas.Bilinear.determinantClass (wallForm Q g) (wallForm_nondegenerate Q g hQ)
    (Module.finBasis F (residual Q g))

/-- Any ordered basis of the residual space computes the same determinant class. -/
theorem wallDeterminantClass_basis (g : Q.IsometryEquiv Q)
    (b : Module.Basis (Fin (Module.finrank F (residual Q g))) F (residual Q g)) :
    wallDeterminantClass Q hQ g =
      Atlas.Bilinear.determinantClass (wallForm Q g) (wallForm_nondegenerate Q g hQ) b :=
  Atlas.Bilinear.determinantClass_basis_independent _ _ _ b

end ClassicalOrthogonal.IntrinsicWall
