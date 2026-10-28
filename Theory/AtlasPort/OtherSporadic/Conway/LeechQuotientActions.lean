/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/LeechQuotientActions.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.LeechCrossKernel
/-!
Central signs, antipodal geometry, and faithful quotient actions for the Leech isometry group.
The proofs identify the actual kernels and transport the concrete actions through the central quotient.

Source: Gerald Höhn, `Atlas/Conway/LeechQuotientActions.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

def quotientCrossRepresentation : LeechCentralQuotient →* Equiv.Perm LeechCross :=
  QuotientGroup.lift leechCentralSigns crossRepresentation (le_of_eq crossRepresentation_kernel.symm)

theorem quotientCrossRepresentation_injective : Function.Injective quotientCrossRepresentation :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr crossRepresentation_kernel.symm

theorem quotientCrossRepresentation_compatible (g : LeechIsometryGroup) :
    quotientCrossRepresentation (leechCentralProjection g) = crossRepresentation g := rfl

def quotientModTwoRepresentation :
    LeechCentralQuotient →* (LeechModTwo ≃ₗ[Bit] LeechModTwo) :=
  QuotientGroup.lift leechCentralSigns leechModTwoRepresentation
    (le_of_eq leechModTwoRepresentation_kernel.symm)

theorem quotientModTwoRepresentation_injective : Function.Injective quotientModTwoRepresentation :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr leechModTwoRepresentation_kernel.symm

theorem quotientModTwoRepresentation_compatible (g : LeechIsometryGroup) :
    quotientModTwoRepresentation (leechCentralProjection g) = leechModTwoRepresentation g := rfl

theorem quotientModTwoRepresentation_quadratic (g : LeechCentralQuotient) (a : LeechModTwo) :
    leechQuadratic (quotientModTwoRepresentation g a) = leechQuadratic a := by
  obtain ⟨h,rfl⟩ := leechCentralProjection_surjective g
  exact leechModTwoRepresentation_quadratic h a

theorem quotientCross_modTwo_equivariant (g : LeechCentralQuotient) (X : LeechCross) :
    (quotientCrossRepresentation g X).val = quotientModTwoRepresentation g X.val := by
  obtain ⟨h,rfl⟩ := leechCentralProjection_surjective g
  rfl

end Atlas.Conway
