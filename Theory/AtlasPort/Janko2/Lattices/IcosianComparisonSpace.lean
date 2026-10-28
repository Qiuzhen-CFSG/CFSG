/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianComparisonSpace.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianComparisonMatrix

/-!
# Icosian Comparison Space

The explicit comparison matrix gives a rational linear equivalence from
three icosian quaternions to the 24 Leech coordinates. Its Gram identity
proves preservation of the weighted rational bilinear form.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianComparisonSpace.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

namespace Atlas.Lattices
open scoped Matrix

/-- Actual rational coordinate isometry. Integral lattice equality is proved separately. -/
noncomputable def icosianComparison : IcosianRationalCoordinates ≃ₗ[ℚ] RationalCoordinates :=
  icosianRealCoordinates.trans
    (Matrix.toLin'OfInv icosianComparison_inverse_matrix icosianComparison_matrix_inverse)

@[simp] theorem icosianComparison_apply (z : IcosianRationalCoordinates) :
    icosianComparison z = icosianComparisonMatrix *ᵥ icosianRealCoordinates z := rfl

@[simp] theorem icosianComparison_symm_apply (x : RationalCoordinates) :
    icosianComparison.symm x =
      icosianRealCoordinates.symm (icosianComparisonInverseMatrix *ᵥ x) := rfl

theorem icosianComparison_isometry (z w : IcosianRationalCoordinates) :
    rationalForm (icosianComparison z) (icosianComparison w) = icosianBilinear z w := by
  rw [icosianBilinear_eq_dot]
  change (1/8 : ℚ) * dotProduct
    (icosianComparisonMatrix *ᵥ icosianRealCoordinates z)
    (icosianComparisonMatrix *ᵥ icosianRealCoordinates w) = _
  rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
    icosianComparison_matrix_gram]
  simp [Matrix.smul_mulVec, dotProduct_smul]

end Atlas.Lattices
