module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteCalculation.Transport
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteCalculation.Scalars.Tables.Certificates

/-!
# Right scalar matrices in the actual integral basis

The checked integer certificates give the basis identities for i, j, k and
(1+i+j+k)/2. Their integer linear combinations then give a single reusable
identity for every Hurwitz unit. This establishes integrality before reduction
modulo two, without computing a rational numerator as a substitute.

The tables retain John Bray and Gerald Höhn's ATLAS attribution and Research
and Attribution License 1.0; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. Source consumer: Aschbacher, Sporadic Groups
(1994), 49.5, pp.283–284.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Algebra Atlas.Lattices Atlas.Codes Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long
namespace ReferenceBlock.ModularCoordinates.FiniteCalculation.Scalars
open Long.Block Long.Block.Realization

open TableCertificates

theorem rightAxis_basis (k : Fin 3) : rightAxis k * basisMatrix =
    basisMatrix * integerMatrix (rightAxisTable k) := by
  have hi := congrArg integerMatrix (axis_integer k)
  simp only [map_mul] at hi
  rw [axis_numerator, basisMatrix]
  change integerMatrix (rightAxisNumerator k) * ((1/2 : ℚ) • integerMatrix basisNumerator) =
    ((1/2 : ℚ) • integerMatrix basisNumerator) * integerMatrix (rightAxisTable k)
  rw [Matrix.mul_smul, Matrix.smul_mul, hi]

theorem rightHalf_basis : rightScalar (1/2) (1/2) (1/2) (1/2) * basisMatrix =
    basisMatrix * integerMatrix rightHalfTable := by
  have hi := congrArg integerMatrix half_integer
  simp only [map_mul, two_smul] at hi
  rw [half_numerator, basisMatrix]
  change ((1/2 : ℚ) • integerMatrix (rightInteger 1 1 1 1)) *
    ((1/2 : ℚ) • integerMatrix basisNumerator) =
      ((1/2 : ℚ) • integerMatrix basisNumerator) * integerMatrix rightHalfTable
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hi]
  simp only [map_add, map_mul, smul_add, ← add_smul]
  norm_num

/-- Integral linear combinations of the identity, the axes, and the half-unit. -/
def tableCombination (c : Fin 5 → ℤ) : Matrix Index Index ℤ :=
  c 0 • 1 + c 1 • rightAxis0Table + c 2 • rightAxis1Table +
    c 3 • rightAxis2Table + c 4 • rightHalfTable

private def matrixCombination (c : Fin 5 → ℤ) : RealMatrix :=
  c 0 • 1 + c 1 • rightAxis 0 + c 2 • rightAxis 1 +
    c 3 • rightAxis 2 + c 4 • rightScalar (1/2) (1/2) (1/2) (1/2)

private theorem combination_basis (c : Fin 5 → ℤ) :
    matrixCombination c * basisMatrix = basisMatrix * integerMatrix (tableCombination c) := by
  simp only [matrixCombination, tableCombination, add_mul, Matrix.smul_mul,
    Matrix.one_mul, rightAxis_basis, rightHalf_basis, map_add, map_zsmul, map_one,
    mul_add, Matrix.mul_smul, Matrix.mul_one]
  rfl

private theorem combination_eq (c : Fin 5 → ℤ) :
    rightScalar ((c 0 : ℚ) + (c 4 : ℚ)/2) ((c 1 : ℚ) + (c 4 : ℚ)/2)
      ((c 2 : ℚ) + (c 4 : ℚ)/2) ((c 3 : ℚ) + (c 4 : ℚ)/2) = matrixCombination c := by
  ext ⟨i,k⟩ ⟨j,l⟩
  simp only [matrixCombination, Matrix.add_apply, Matrix.smul_apply]
  by_cases h : i = j
  · subst j
    fin_cases k <;> fin_cases l <;>
      simp [rightAxis, rightScalar, rightQuaternion, zsmul_eq_mul,
        Matrix.cons_val_two, Matrix.cons_val_three, -Matrix.cons_val] <;> ring
  · simp [rightAxis, rightScalar, h, Matrix.cons_val_two, -Matrix.cons_val]

theorem combination_coordinates (c : Fin 5 → ℤ) :
    rightScalar ((c 0 : ℚ) + (c 4 : ℚ)/2) ((c 1 : ℚ) + (c 4 : ℚ)/2)
      ((c 2 : ℚ) + (c 4 : ℚ)/2) ((c 3 : ℚ) + (c 4 : ℚ)/2) * basisMatrix =
        basisMatrix * (tableCombination c).map (Int.castRingHom ℚ) := by
  rw [combination_eq]
  exact combination_basis c

end ReferenceBlock.ModularCoordinates.FiniteCalculation.Scalars
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
