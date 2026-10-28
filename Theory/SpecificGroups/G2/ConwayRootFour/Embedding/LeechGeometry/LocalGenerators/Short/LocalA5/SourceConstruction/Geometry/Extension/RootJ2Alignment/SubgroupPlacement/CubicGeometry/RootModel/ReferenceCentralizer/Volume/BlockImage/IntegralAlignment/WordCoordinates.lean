module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.IntegralAlignment.WordData
/-!
# Checked coordinate equations for the integral reference word

The quaternion-coordinate formula is proved from the existing faithful matrix
homomorphism. Integer identities then verify the generator comparisons and each
prefix of the word. All arithmetic is kernel-checked; these finite certificates
are connected to actual integral Leech isometries in Word.

The data retain the ATLAS attribution and license documented in WordData.
-/

set_option Elab.async false
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Atlas.Conway Atlas.Algebra Atlas.Lattices Matrix
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long
open Long.Block Long.Block.Realization
namespace IntegralAlignment

open Sporadic.LeechRelated.J2.IcosianComparison.Generators
open Sporadic.LeechRelated.J2.IcosianComparison.Generators.RelatorMatrices

def hermitianRealMatrix (M : QMatrix) : Matrix IcosianRealIndex IcosianRealIndex ℚ :=
  fun i j => icosianRealCoordinates
    (M *ᵥ icosianRealCoordinates.symm (Pi.single j 1)) i

theorem hermitianRealMatrix_apply (g : icosianHermitianGroup) (z : IcosianRationalCoordinates) :
    icosianRealCoordinates (g.val z) =
      hermitianRealMatrix (matrixHom g) *ᵥ icosianRealCoordinates z := by
  let f := icosianRealCoordinates.symm.trans (g.val.trans icosianRealCoordinates)
  have hm : LinearMap.toMatrix' f.toLinearMap = hermitianRealMatrix (matrixHom g) := by
    ext i j
    exact congrArg (fun z => icosianRealCoordinates z i)
      (apply_eq_matrix g (icosianRealCoordinates.symm (Pi.single j 1)))
  rw [← hm, LinearMap.toMatrix'_mulVec]
  change _ = icosianRealCoordinates (g.val (icosianRealCoordinates.symm (icosianRealCoordinates z)))
  rw [icosianRealCoordinates.symm_apply_apply]

open WordData

/-- The three quaternion matrices in the exact retained icosian coordinates. -/
theorem hermitian_specifications :
    hermitianRealMatrix mx = (1/4 : ℚ) • xIcosianNumerator.map (Int.castRingHom ℚ) ∧
    hermitianRealMatrix my = (1/4 : ℚ) • yIcosianNumerator.map (Int.castRingHom ℚ) ∧
    hermitianRealMatrix comm4 = (1/4 : ℚ) • referenceIcosianNumerator.map (Int.castRingHom ℚ) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- The two block factors and the exact Eisenstein scalar action. -/
theorem block_specifications :
    realification matrixA.conjTranspose = (1/2 : ℚ) • aNumerator.map (Int.castRingHom ℚ) ∧
    realification matrixBInv.conjTranspose = (1/2 : ℚ) • bNumerator.map (Int.castRingHom ℚ) ∧
    ReferenceBlock.cubicMatrix false = (1/2 : ℚ) • omegaNumerator.map (Int.castRingHom ℚ) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- The comparison to the actual x, y and commutator-fourth-power lifts. -/
theorem comparison_certificates :
    (2 : ℤ) • (Long.Block.Realization.IcosianComparison.numerator * xNumerator) =
      xIcosianNumerator * Long.Block.Realization.IcosianComparison.numerator ∧
    (2 : ℤ) • (Long.Block.Realization.IcosianComparison.numerator * yNumerator) =
      yIcosianNumerator * Long.Block.Realization.IcosianComparison.numerator ∧
    (2 : ℤ) • (Long.Block.Realization.IcosianComparison.numerator * referenceNumerator) =
      referenceIcosianNumerator * Long.Block.Realization.IcosianComparison.numerator := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

end IntegralAlignment
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
