module

public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Trio.Spaces
public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Trio.FixedCommutators.FixedSpace
public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Trio.FixedCommutators.PlaneAction
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.Affine
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.FixedCommutators

/-!
# Standard-trio cocode commutators and the geometric fixed three-space

For the standard marking, both the intrinsic two-core and the mapped
intrinsic solvable residual generate exactly the geometric nine-dimensional
pair space by cocode displacements. The two-core fixed space is exactly the
three-dimensional affine-plane range, which lies in the pair space. The
native affine lifts realize every linear automorphism of this fixed space;
the fixed-space equality discharges the lower-action helper's premise.

These results establish the standard-marking fixed-space, lower-action and
commutator branches of H.15.6(1–2). Arbitrary-trio transport, the top action,
the chief factors and the tensor identification belong to the parent assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.15.6(1–2),
printed p.401. This module uses the native M24 cocode and intrinsic residuals.
-/

public section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open MathieuCode Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
noncomputable section

/-- The pair space is the commutator of the actual intrinsic two-core. -/
theorem standard_trioPairSpace_eq_kernel_commutator :
    trioPairSpace standardTrio =
      subspaceCommutator cocodeRepresentation ⊤ (trioKernel standardTrio) :=
  TrioCalculation.standard_pairSpace_eq_twoCore_commutator

/-- The residual is the mapped intrinsic solvable residual from `Spaces`. -/
theorem standard_trioPairSpace_eq_residual_commutator :
    trioPairSpace standardTrio =
      subspaceCommutator cocodeRepresentation ⊤ (trioResidual standardTrio) :=
  TrioCalculation.standard_pairSpace_eq_residual_commutator

theorem standard_planeRange_le_trioFixedSpace :
    TrioCalculation.standardPlaneMap.range ≤ trioFixedSpace standardTrio :=
  TrioCalculation.standardPlaneMap_range_le_fixedSpace

theorem standard_planeRange_le_trioPairSpace :
    TrioCalculation.standardPlaneMap.range ≤ trioPairSpace standardTrio :=
  TrioCalculation.standardPlaneMap_range_le_pairSpace

theorem three_le_finrank_standard_trioFixedSpace :
    3 ≤ Module.finrank (ZMod 2) (trioFixedSpace standardTrio) := by
  rw [← TrioCalculation.finrank_standardPlaneMap_range]
  exact Submodule.finrank_mono standard_planeRange_le_trioFixedSpace

/-- The fixed space of the intrinsic standard-trio two-core has dimension three. -/
theorem finrank_standard_trioFixedSpace :
    Module.finrank (ZMod 2) (trioFixedSpace standardTrio) = 3 := by
  rw [standard_trioFixedSpace_eq_planeRange]
  exact TrioCalculation.finrank_standardPlaneMap_range

/-- The intrinsic fixed three-space lies inside the geometric pair space. -/
theorem standard_trioFixedSpace_le_trioPairSpace :
    trioFixedSpace standardTrio ≤ trioPairSpace standardTrio := by
  rw [standard_trioFixedSpace_eq_planeRange]
  exact standard_planeRange_le_trioPairSpace

/-- The actual trio stabilizer induces the full general linear group on its
intrinsic two-core fixed space. -/
theorem standard_trioFixedSubrepresentation_surjective :
    Function.Surjective
      ((trioFixedSubrepresentation standardTrio).toRepresentation.asGroupHom) :=
  standard_trioFixedSubrepresentation_surjective_of_eq_planeRange
    standard_trioFixedSpace_eq_planeRange

end
end CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
