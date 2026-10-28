module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Graph.Checks

/-!
# Rational consequences of the integral graph certificates

The denominator-cleared certificates imply square minus identity, preservation
of the actual glued integral basis, and preservation of its rational Gram form.
These are the three inputs used to construct the genuine integral Leech swap.
See `Data` for source and coordinate conventions.
-/

@[expose] public section
open Matrix Atlas.Algebra
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Graph
open Block Block.Realization

theorem swapMatrix_square : swapMatrix * swapMatrix = -1 := by
  have h := congrArg integerMatrix integerCertificates.1
  simp only [map_mul, map_neg, map_ofNat] at h
  rw [swapMatrix, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h]
  ext i j
  by_cases he : i=j <;> norm_num [Matrix.smul_apply, Matrix.ofNat_apply, Matrix.one_apply, he]

theorem swapMatrix_basis : swapMatrix * basisMatrix = basisMatrix * integerMatrix coordinates := by
  have h := congrArg integerMatrix integerCertificates.2.1
  simp only [map_mul, two_smul, map_add] at h
  change integerMatrix numerator * integerMatrix basisNumerator =
    integerMatrix basisNumerator * integerMatrix coordinates +
    integerMatrix basisNumerator * integerMatrix coordinates at h
  change ((1/2 : ℚ) • integerMatrix numerator) * ((1/2 : ℚ) • integerMatrix basisNumerator) =
    ((1/2 : ℚ) • integerMatrix basisNumerator) * integerMatrix coordinates
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, smul_add, ← add_smul, Matrix.smul_mul]
  norm_num

theorem swapMatrix_gram : swapMatrix.transpose * gramMatrix * swapMatrix = gramMatrix := by
  have h1 := congrArg integerMatrix integerCertificates.2.2.1
  have h2 := congrArg integerMatrix integerCertificates.2.2.2
  simp only [map_mul] at h1 h2
  change integerMatrix IcosianComparison.integralGram * integerMatrix numerator =
    integerMatrix gramProduct at h1
  change (integerMatrix numerator).transpose * integerMatrix gramProduct =
    integerMatrix ((4 : ℤ) • IcosianComparison.integralGram) at h2
  have hc : integerMatrix ((4 : ℤ) • IcosianComparison.integralGram) =
      (4 : ℚ) • integerMatrix IcosianComparison.integralGram := by
    rw [map_zsmul]
    exact (Int.cast_smul_eq_zsmul ℚ (4 : ℤ) _).symm
  rw [hc] at h2
  rw [IcosianComparison.specifications.2.2.1]
  change swapMatrix.transpose * integerMatrix IcosianComparison.integralGram * swapMatrix = _
  simp only [swapMatrix, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [Matrix.mul_assoc, h1, h2, smul_smul]
  norm_num
  rfl

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Graph
