module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.Lattice
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.IcosianComparison.Checks

/-!
# The rational quaternion comparison

The checked inverse matrices construct an actual rational linear equivalence.
The denominator-cleared Gram identity proves preservation of the bilinear
form; intermediate integer matrices retain its literal Golay-coordinate images.
This is the explicit comparison of the John Bray quaternion lattice with Gerald
Höhn's ATLAS icosian coordinates, with attribution retained in `Data`.

-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Atlas.Algebra Atlas.Lattices Atlas.Codes
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization
namespace IcosianComparison

private theorem candidate_eq_half :
    comparisonCandidateMatrix = (1/2 : ℚ) • numerator.map (Int.castRingHom ℚ) :=
  specifications.1
private theorem inverse_eq_quarter :
    comparisonInverseMatrix = (1/4 : ℚ) • inverseNumerator.map (Int.castRingHom ℚ) :=
  specifications.2.1
private theorem gram_eq : gramMatrix = integralGram.map (Int.castRingHom ℚ) :=
  specifications.2.2.1
private theorem coordinate_eq :
    icosianComparisonMatrix = coordinateMatrix.map (Int.castRingHom ℚ) :=
  specifications.2.2.2
private theorem inverse_numerator : inverseNumerator * numerator = 8 :=
  integer_certificates.1
private theorem numerator_inverse : numerator * inverseNumerator = 8 :=
  integer_certificates.2.1
private theorem numerator_gram : numerator.transpose * numerator = (4 : ℤ) • integralGram :=
  integer_certificates.2.2.1
private theorem coordinate_numerator : coordinateMatrix * numerator = (2 : ℤ) • leechMatrix :=
  integer_certificates.2.2.2.1
private theorem leech_basis : leechMatrix * basisNumerator = (2 : ℤ) • basisImages :=
  integer_certificates.2.2.2.2.1

private theorem inverse_candidate : comparisonInverseMatrix * comparisonCandidateMatrix = 1 := by
  have hi := congrArg (fun M => M.map (Int.castRingHom ℚ)) inverse_numerator
  simp only [Matrix.map_mul] at hi
  rw [candidate_eq_half, inverse_eq_quarter, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hi]
  ext i j
  by_cases h : i=j <;> norm_num [Matrix.smul_apply, Matrix.ofNat_apply, Matrix.one_apply, h]

private theorem candidate_inverse : comparisonCandidateMatrix * comparisonInverseMatrix = 1 := by
  have hi := congrArg (fun M => M.map (Int.castRingHom ℚ)) numerator_inverse
  simp only [Matrix.map_mul] at hi
  rw [candidate_eq_half, inverse_eq_quarter, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hi]
  ext i j
  by_cases h : i=j <;> norm_num [Matrix.smul_apply, Matrix.ofNat_apply, Matrix.one_apply, h]

private theorem candidate_gram : comparisonCandidateMatrix.transpose * comparisonCandidateMatrix = gramMatrix := by
  have hi := congrArg (fun M => M.map (Int.castRingHom ℚ)) numerator_gram
  simp only [show (4 : ℤ) = 2 + 2 from rfl, add_smul, two_smul,
    Matrix.map_mul, Matrix.transpose_map] at hi
  rw [candidate_eq_half, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hi, gram_eq]
  ext i j
  norm_num [Matrix.smul_apply, Matrix.map_apply]
  ring

private theorem candidate_leech : icosianComparisonMatrix * comparisonCandidateMatrix =
    leechMatrix.map (Int.castRingHom ℚ) := by
  have hi := congrArg (fun M => M.map (Int.castRingHom ℚ)) coordinate_numerator
  simp only [Matrix.map_mul] at hi
  rw [candidate_eq_half, coordinate_eq, Matrix.mul_smul, hi]
  ext i j
  norm_num [Matrix.smul_apply, Matrix.map_apply]
  ring

theorem candidate_basis : icosianComparisonMatrix * comparisonCandidateMatrix * basisMatrix =
    basisImages.map (Int.castRingHom ℚ) := by
  have hi := congrArg (fun M => M.map (Int.castRingHom ℚ)) leech_basis
  simp only [Matrix.map_mul] at hi
  rw [candidate_leech, basisMatrix, Matrix.mul_smul]
  change (1/2 : ℚ) • (leechMatrix.map (Int.castRingHom ℚ) * basisNumerator.map (Int.castRingHom ℚ)) = _
  rw [hi]
  ext i j
  norm_num [Matrix.smul_apply, Matrix.map_apply]
  ring

end IcosianComparison

/-- The explicit, unconditional comparison with the rational icosian space. -/
def quaternionComparison : Space ≃ₗ[ℚ] IcosianRationalCoordinates :=
  (Matrix.toLin'OfInv (M := comparisonInverseMatrix) (M' := comparisonCandidateMatrix)
    (by exact IcosianComparison.inverse_candidate)
    (by exact IcosianComparison.candidate_inverse)).trans icosianRealCoordinates.symm

/-- Evaluation in precisely the coordinate convention of `ComparisonData`. -/
theorem quaternionComparison_coordinates (x : Space) :
    icosianRealCoordinates (quaternionComparison x) = comparisonCandidateMatrix *ᵥ x :=
  icosianRealCoordinates.apply_symm_apply _

theorem quaternionComparison_symm_apply (z : IcosianRationalCoordinates) :
    quaternionComparison.symm z = comparisonInverseMatrix *ᵥ icosianRealCoordinates z := rfl

/-- The candidate preserves the actual weighted icosian form. -/
theorem quaternionComparison_form (x y : Space) :
    icosianBilinear (quaternionComparison x) (quaternionComparison y) = form x y := by
  rw [icosianBilinear_eq_dot, quaternionComparison_coordinates, quaternionComparison_coordinates,
    dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
    IcosianComparison.candidate_gram]
  rfl

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization
