/-
Uses Gerald Höhn's retained ATLAS icosian coordinates, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917. Distributed under the ATLAS
Research and Attribution License 1.0; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Tetrahedral.Reference
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Tetrahedral.Outer.Twist

/-!
# Correcting the semilinear symmetry to centralize the reference cubic

The correction is the literal four-reflection word
(axis 1)(diagonal 2)(transition 3)(diagonal 1). Its sparse quaternion matrix
intertwines `comm4` with the semilinear transform of `comm4`. Consequently
its inverse times the twist commutes with the reference already in Co₀,
and hence centralizes the cyclic reference subgroup in the original Co₁.
No cubic fusion, centralizer classification, or tetrahedral orbit is used.

Source application: Aschbacher, *Sporadic Groups* (1994), 49.5, p.284.
The literal reference word and central-sign projection are those of
`RootModel.Reference`; the reflections are the retained ATLAS lattice maps.
-/

open Atlas.Algebra Atlas.Lattices Atlas.Conway
open scoped Matrix
open Sporadic.LeechRelated.J2.IcosianComparison.Generators
open Sporadic.LeechRelated.J2.IcosianComparison.Generators.RelatorMatrices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.Outer
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance : DecidableEq IcosianQuaternion := fun a b =>
  decidable_of_iff (a.re = b.re ∧ a.imI = b.imI ∧ a.imJ = b.imJ ∧ a.imK = b.imK)
    QuaternionAlgebra.ext_iff.symm

def correctionLift : icosianHermitianGroup :=
  icosianAxisReflection 1 * icosianReflectionDiagonalGenerator 2 *
    icosianAxisTransitionGenerator 3 * icosianReflectionDiagonalGenerator 1

private def correctionMatrix : QMatrix :=
  !![-icosianI, 0, 0; 0, 0, -icosianK; 0, -icosianJ, 0]

private theorem correctionLift_matrix : matrixHom correctionLift = correctionMatrix := by
  have hd1 : matrixHom (icosianReflectionDiagonalGenerator 1) = d1 := by decide +kernel
  have hd2 : matrixHom (icosianReflectionDiagonalGenerator 2) = d2 := by decide +kernel
  have ht3 : matrixHom (icosianAxisTransitionGenerator 3) = t3 := by decide +kernel
  have ha : matrixHom (icosianAxisReflection 1) =
      (!![1, 0, 0; 0, -1, 0; 0, 0, 1] : QMatrix) := by
    apply Matrix.ext
    intro i j
    change (icosianAxisReflection 1).val (Pi.single j 1) i = _
    rw [icosianAxisReflection_apply]
    fin_cases i <;> fin_cases j <;> simp
  simp only [correctionLift, map_mul, ha, hd2, ht3, hd1]
  decide +kernel

private theorem correctionMatrix_intertwines :
    correctionMatrix * comm4 = (show QMatrix from fun i j => sigmaQuaternion (comm4 i j)) * correctionMatrix := by
  decide +kernel

private theorem correctionLift_intertwines (v : IcosianRationalCoordinates) :
    correctionLift.val (RootModel.referenceLift.val v) =
      (show QMatrix from fun i j => sigmaQuaternion (comm4 i j)).mulVec (correctionLift.val v) := by
  simp only [apply_eq_matrix]
  change (matrixHom correctionLift).mulVec ((matrixHom RootModel.referenceLift).mulVec v) =
    (show QMatrix from fun i j => sigmaQuaternion (comm4 i j)).mulVec ((matrixHom correctionLift).mulVec v)
  rw [correctionLift_matrix, RootModel.referenceLift_matrix, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, correctionMatrix_intertwines]

private theorem twist_reference (v : IcosianRationalCoordinates) :
    twist (RootModel.referenceLift.val v) =
      (show QMatrix from fun i j => sigmaQuaternion (comm4 i j)).mulVec (twist v) := by
  rw [apply_eq_matrix]
  change twist ((matrixHom RootModel.referenceLift).mulVec v) = _
  rw [RootModel.referenceLift_matrix]
  exact twist_mulVec _ _

theorem corrected_twist_commute :
    Commute (correctionLift.val⁻¹ * twist) RootModel.referenceLift.val := by
  apply LinearEquiv.ext
  intro v
  simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv]
  apply correctionLift.val.injective
  rw [LinearEquiv.apply_symm_apply, correctionLift_intertwines, LinearEquiv.apply_symm_apply]
  exact twist_reference v

def correctedCo0 : LeechIsometryGroup := (icosianHermitianToCo0 correctionLift)⁻¹ * twistCo0

theorem correctedCo0_commute : Commute correctedCo0 (icosianHermitianToCo0 RootModel.referenceLift) := by
  apply fullIsometryEquiv.injective
  simp only [correctedCo0, map_mul, map_inv, icosianHermitianToCo0_extension, twistCo0_extension]
  apply Subtype.ext
  change Commute
    ((icosianAutomorphismComparison correctionLift.val)⁻¹ * icosianAutomorphismComparison twist)
    (icosianAutomorphismComparison RootModel.referenceLift.val)
  simpa only [map_mul, map_inv] using corrected_twist_commute.map icosianAutomorphismComparison

def correctedCo1 : LeechCentralQuotient := leechCentralProjection correctedCo0

theorem correctedCo1_centralizes : correctedCo1 ∈ referenceCubicCentralizer := by
  have h : Commute correctedCo1 RootModel.referenceCubic :=
    correctedCo0_commute.map leechCentralProjection
  intro z hz
  obtain ⟨n, rfl⟩ := hz
  exact (h.zpow_right n).symm.eq

end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.Outer
