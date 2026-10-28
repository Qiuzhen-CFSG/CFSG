/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianScalarFaithfulness.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Source revision: 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianScalarIsometries
public import Theory.AtlasPort.Janko2.Algebra.IcosianNormOneCard

/-!
# IcosianScalarFaithfulness

Right scalar units act faithfully on the rational coordinate space and the Leech lattice.
Evaluation on a unit coordinate proves injectivity and transfers the scalar-group order 120 to the image.

Source: Gerald Höhn, `Atlas/Conway/IcosianScalarFaithfulness.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and the definition bodies
needed by the source coordinate calculations; source statements are preserved.
-/

set_option backward.isDefEq.respectTransparency false
public section

namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

theorem icosianScalarRepresentation_injective :
    Function.Injective icosianScalarRepresentation := by
  intro u v h
  have he := congrArg (fun f : IcosianRationalCoordinates ≃ₗ[ℚ] IcosianRationalCoordinates =>
    f (fun _ => 1) 0) h
  have hu : (Unitary.toUnits u.val)⁻¹=(Unitary.toUnits v.val)⁻¹ := by
    apply Units.ext
    simpa [icosianScalarRepresentation,icosianRightUnitEquiv,icosianRightMul] using he
  apply Subtype.ext
  exact Unitary.toUnits_injective (inv_inj.mp hu)

theorem icosianScalarsToCo0_injective : Function.Injective icosianScalarsToCo0 := by
  intro u v h
  apply icosianScalarRepresentation_injective
  apply icosianAutomorphismComparison.injective
  have he := congrArg (fun g : LeechIsometryGroup => (fullIsometryEquiv g).val) h
  rw [icosianScalarsToCo0_extension,icosianScalarsToCo0_extension] at he
  exact he

theorem icosianScalarsToCo0_range_card : Nat.card icosianScalarsToCo0.range=120 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective icosianScalarsToCo0_injective).toEquiv]
  exact icosianNormOneGroup_card

end Atlas.Conway
