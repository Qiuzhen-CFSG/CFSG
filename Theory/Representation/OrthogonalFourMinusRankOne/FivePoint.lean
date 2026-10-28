module

public import Theory.Representation.SL2.BinarySmallModels
public import Theory.Representation.OrthogonalFourMinusHermitianEquiv
public import Theory.Representation.BinaryPermutation.FiveGeometry
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The Hermitian/five-point comparison contract

The degree-four binary orthogonal action is the augmentation core of the
five-point permutation action. A comparison must identify both the acting
groups and their actions, and preserve the determinant quadratic form. These
requirements distinguish it from the natural two-dimensional SL₂(4) action.

This module publishes the precise construction interface. Its existence is a
separate mathematical obligation; no comparison is postulated here.
Source: Aschbacher–Smith, K.3.1.2, printed p.454, and B.3, printed pp.83–84.
-/

@[expose] public noncomputable section
namespace Representation.OrthogonalFourMinus.FivePoint
open FiniteModel HermitianEquiv

local instance : Algebra (ZMod 2) (fixedField 1) := ZMod.algebra _ 2
local instance : Module (ZMod 2) (Space 1) :=
  Module.compHom (Space 1) (algebraMap (ZMod 2) (fixedField 1))

/-- The actual group comparison, binary intertwiner, and quadratic compatibility. -/
structure Comparison where
  groupEquiv : Matrix.SpecialLinearGroup (Fin 2) (Field 1) ≃* alternatingGroup (Fin 5)
  coordinates : Space 1 ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5)
  intertwines : ∀ g v, coordinates (SL2.BinarySmall.hermitian 1 g v) =
    BinaryPermutation.coreRepresentation (Fin 5) (groupEquiv g).val (coordinates v)
  preserves_form : ∀ v, form 1 v =
    algebraMap (ZMod 2) (fixedField 1) (BinaryPermutation.FiveGeometry.form (coordinates v))

/-- The five-point form agrees with the existing literal minus form through
the already proved Hermitian isometry. -/
theorem Comparison.minus_form (C : Comparison) (v : Space 1) :
    ClassicalOrthogonal.Minus.quadraticForm (fixedField 1) 2
      (hermitianMinusIsometry 1 v) =
    algebraMap (ZMod 2) (fixedField 1) (BinaryPermutation.FiveGeometry.form (C.coordinates v)) :=
  ((hermitianMinusIsometry 1).map_app v).trans (C.preserves_form v)

end Representation.OrthogonalFourMinus.FivePoint
