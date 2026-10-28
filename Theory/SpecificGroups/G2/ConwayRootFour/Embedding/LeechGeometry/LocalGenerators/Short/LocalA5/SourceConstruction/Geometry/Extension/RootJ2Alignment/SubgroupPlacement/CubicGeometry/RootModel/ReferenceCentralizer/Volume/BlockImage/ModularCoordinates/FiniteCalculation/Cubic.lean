module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteModel
/-!
# Integral coordinates of both left cubic orientations

One integer matrix identity clears the denominators in the actual glued
quaternion basis. Multiplying by the checked inverse basis identifies the
result with the published numerator definition. The inverse cubic equals
minus identity minus the forward cubic, so its integrality follows without
a second dense rational calculation.

Source consumer: Aschbacher, Sporadic Groups (1994), 49.5, pp.283–284.
The derived table retains John Bray's ATLAS 6L34G1-Ar6aB0 and Gerald Höhn
integral-comparison attribution. See LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Algebra Atlas.Lattices Atlas.Codes Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long
namespace ReferenceBlock.ModularCoordinates
open Long.Block Long.Block.Realization
namespace FiniteCalculation

private def cubicNumerator : Matrix Index Index ℤ := fun i j =>
  if i.1 = j.1 then
    (!![-1,-1,-1,-1;1,-1,-1,1;1,1,-1,-1;1,-1,1,-1] : Matrix (Fin 4) (Fin 4) ℤ) i.2 j.2
  else 0

def forwardCubicTable : Matrix Index Index ℤ := fun i j =>
  (![
    ![-1,-1,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,-1,-1,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![-1,-1,-1,0,-1,-1,-1,0,-2,-1,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0],
    ![1,1,1,1,0,1,1,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,1,0,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,1,1,0,0,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,-1,-1,-1,-1,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1,-1,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],
    ![-1,-1,-1,0,0,0,0,0,0,0,0,0,-1,-1,-1,0,-2,-1,-1,-1,0,0,0,0],
    ![0,1,1,0,0,0,0,0,0,0,0,0,0,1,1,0,1,0,0,1,0,0,0,0],
    ![1,1,1,1,0,0,0,0,0,0,0,0,1,1,1,1,1,1,0,0,0,0,0,0],
    ![0,0,1,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,0,0,0,0],
    ![-1,-1,-1,0,-1,-1,-1,0,0,0,0,0,-1,-1,-1,0,0,0,0,0,-2,-1,-1,-1],
    ![1,1,1,1,0,1,1,0,0,0,0,0,1,1,1,1,0,0,0,0,1,0,0,1],
    ![0,0,1,0,1,1,1,1,0,0,0,0,0,0,1,0,0,0,0,0,1,1,0,0],
    ![0,1,1,0,0,0,1,0,0,0,0,0,0,1,1,0,0,0,0,0,1,0,1,0]] : Matrix (Fin 24) (Fin 24) ℤ) (indexNumber i) (indexNumber j)

private theorem cubic_numerator : cubicMatrix false =
    (1/2 : ℚ) • integerMatrix cubicNumerator := by decide +kernel

private theorem cubic_integer : cubicNumerator * basisNumerator =
    2 • (basisNumerator * forwardCubicTable) := by decide +kernel

private theorem forward_basis : cubicMatrix false * basisMatrix =
    basisMatrix * forwardCubicTable.map (Int.castRingHom ℚ) := by
  have hi := congrArg integerMatrix cubic_integer
  simp only [map_mul, two_smul] at hi
  rw [cubic_numerator, basisMatrix]
  change ((1/2 : ℚ) • integerMatrix cubicNumerator) *
    ((1/2 : ℚ) • integerMatrix basisNumerator) =
    ((1/2 : ℚ) • integerMatrix basisNumerator) * integerMatrix forwardCubicTable
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hi]
  simp only [map_add, map_mul, smul_add, ← add_smul]
  norm_num

private theorem inverse_eq : cubicMatrix true = -1 - cubicMatrix false := by decide +kernel

def cubicTable (inverse : Bool) : Matrix Index Index ℤ :=
  if inverse then -1 - forwardCubicTable else forwardCubicTable

theorem cubicTable_basis (inverse : Bool) : cubicMatrix inverse * basisMatrix =
    basisMatrix * (cubicTable inverse).map (Int.castRingHom ℚ) := by
  cases inverse
  · exact forward_basis
  · rw [inverse_eq, sub_mul, neg_mul, Matrix.one_mul, forward_basis]
    change -basisMatrix - basisMatrix * integerMatrix forwardCubicTable =
      basisMatrix * integerMatrix (-1 - forwardCubicTable)
    rw [map_sub, map_neg, map_one, mul_sub, mul_neg, Matrix.mul_one]

theorem cubicCoordinates_eq_table (inverse : Bool) :
    cubicCoordinates inverse = cubicTable inverse := by
  have h := congrArg (fun M : RealMatrix => basisInverse.map (Int.castRingHom ℚ) * M)
    (cubicTable_basis inverse)
  simp only [← Matrix.mul_assoc, inverse_mul_basis, Matrix.one_mul] at h
  ext i j
  change ((basisInverse.map (Int.castRingHom ℚ) * cubicMatrix inverse * basisMatrix) i j).num = _
  rw [h]
  simp

end FiniteCalculation

/-- Both published numerator matrices are the exact integral coordinate matrices. -/
theorem cubicCoordinates_integral (inverse : Bool) : CubicIntegral inverse := by
  unfold CubicIntegral
  rw [FiniteCalculation.cubicCoordinates_eq_table]
  exact FiniteCalculation.cubicTable_basis inverse
end ReferenceBlock.ModularCoordinates
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
