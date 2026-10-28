/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianScalarStructure.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianHermitianIdentities
public import Theory.AtlasPort.Janko2.Algebra.IcosianOrderBasis

/-!
# Icosian Scalar Structure

Preservation of the weighted rational pairing together with right
scalar linearity implies preservation of the quaternion-valued Hermitian
form. Scalar tests recover every component of the pairing.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianScalarStructure.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Lattices
open Atlas.Algebra
open scoped BigOperators Quaternion QuadraticAlgebra

def icosianRightMulLinear (a : IcosianQuaternion) : Module.End ℚ IcosianRationalCoordinates where
  toFun x := icosianRightMul x a
  map_add' x y := by funext j; exact add_mul _ _ _
  map_smul' r x := by funext j; exact Algebra.smul_mul_assoc r (x j) a

/-- The weighted rational pairing and right-scalar linearity recover the complete
quaternion-valued Hermitian form. -/
theorem icosianHermitian_of_bilinear_and_right_linear
    (f : IcosianRationalCoordinates → IcosianRationalCoordinates)
    (hf : ∀ x y,icosianBilinear (f x) (f y)=icosianBilinear x y)
    (hl : ∀ a x,f (icosianRightMul x a)=icosianRightMul (f x) a) :
    ∀ x y,icosianHermitian (f x) (f y)=icosianHermitian x y := by
  intro x y
  apply icosianFunctional_pairing_ext
  intro a
  rw [icosianFunctional_mul_comm a,icosianFunctional_mul_comm a]
  have h := hf x (icosianRightMul y a)
  rw [hl] at h
  simp only [icosianBilinear,icosianHermitian_rightMul_right] at h
  linarith

end Atlas.Lattices
