/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianIntegralScalarCompatibility.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Source revision: 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianIntegralScalarAction
public import Theory.AtlasPort.Janko2.Conway.IcosianScalarIsometries

/-!
# IcosianIntegralScalarCompatibility

The integral right-scalar endomorphism for an inverse unit agrees with its
Leech isometry. The lattice comparison and uniqueness of rational extension prove this compatibility.

Source: Gerald Höhn, `Atlas/Conway/IcosianIntegralScalarCompatibility.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and the definition bodies
needed by the source coordinate calculations; source statements are preserved.
-/

set_option backward.isDefEq.respectTransparency false
public section

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

/-- The previously constructed scalar-unit isometry is exactly the integral
endomorphism belonging to its inverse right scalar. -/
theorem icosianLeechRightScalars_unit (u : icosianNormOneGroup) (x : leech) :
    icosianLeechRightScalars (MulOpposite.op (icosianNormOneToOrder (u⁻¹))) x=
      (icosianScalarsToCo0 u).val x := by
  obtain ⟨z,rfl⟩ := icosianLeechEquiv.surjective x
  apply Subtype.ext
  apply rationalEmbedding_injective
  rw [icosianLeechRightScalars_rational]
  have h := congrArg (fun f : rationalLatticeIsometries =>
    f.val (icosianComparison (icosianCoordinateEmbedding z.val)))
      (icosianScalarsToCo0_extension u)
  change rationalExtension (icosianScalarsToCo0 u).val
      (icosianComparison (icosianCoordinateEmbedding z.val))=
    icosianRationalScalar u (icosianComparison (icosianCoordinateEmbedding z.val)) at h
  rw [← icosianLeechEquiv_agrees,rationalExtension_agrees] at h
  rw [h]
  rw [icosianLeechEquiv_agrees]
  change icosianComparison (fun i => (z.val i).val*(icosianNormOneToOrder (u⁻¹)).val)=
    icosianComparison (icosianScalarRepresentation u
      (icosianComparison.symm (icosianComparison (icosianCoordinateEmbedding z.val))))
  rw [icosianComparison.symm_apply_apply]
  rfl

end Atlas.Conway
