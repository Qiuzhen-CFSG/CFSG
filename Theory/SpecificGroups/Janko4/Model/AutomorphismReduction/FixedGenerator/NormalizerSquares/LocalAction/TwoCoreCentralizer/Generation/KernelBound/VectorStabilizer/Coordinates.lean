module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.CoordinatesData

/-!
# A certified basis adapted to the involution

The existing E,H,L columns form a basis of the full 112-dimensional module.
Packed row products check both inverse identities; the rectangular projection
identities then yield reconstruction and the exact displacement map E times
the third projection. The invariant form pairs E and L by the published J,
and vanishes on E-by-E and E-by-H. No restriction on a general group element
is inferred from numerical dimensions.

The source and witness-generation conventions are in source/README.md and
Model.Data. These coordinates are used by the full block reduction in Blocks.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership GeneratorCertificates

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem adaptedBasis_mul_inverse : adaptedBasis * adaptedInverse = 1 := by
  change rectDecode 112 adaptedBasisRows * rectDecode 112 adaptedInverseRows = 1
  rw [← rectDecode_one 112]
  apply rectProduct_eq
  simp only [get_ofFn]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem adaptedInverse_mul_basis : adaptedInverse * adaptedBasis = 1 := by
  change rectDecode 112 adaptedInverseRows * rectDecode 112 adaptedBasisRows = 1
  rw [← rectDecode_one 112]
  apply rectProduct_eq
  simp only [get_ofFn]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem adaptedBasis_image :
    adaptedBasis.submatrix id imageIndex = restrictionEmbedding := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem adaptedBasis_homology :
    adaptedBasis.submatrix id homologyIndex = mixedEmbedding := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem adaptedBasis_lifts :
    adaptedBasis.submatrix id liftIndex = restrictionLifts := by decide +kernel

private theorem inverse_basis_submatrix {m n : Type*} (r : m → Fin 112) (c : n → Fin 112) :
    adaptedInverse.submatrix r id * adaptedBasis.submatrix id c =
      (1 : BinaryMatrix).submatrix r c := by
  have h := Matrix.submatrix_mul_equiv adaptedInverse adaptedBasis r (Equiv.refl _) c
  simpa only [Equiv.coe_refl, adaptedInverse_mul_basis] using h

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem imageProjection_embedding : imageProjection * restrictionEmbedding = 1 := by
  rw [← adaptedBasis_image]
  change adaptedInverse.submatrix imageIndex id * adaptedBasis.submatrix id imageIndex = 1
  rw [inverse_basis_submatrix]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem homologyProjection_embedding : homologyProjection * restrictionEmbedding = 0 := by
  rw [← adaptedBasis_image]
  change adaptedInverse.submatrix homologyIndex id * adaptedBasis.submatrix id imageIndex = 0
  rw [inverse_basis_submatrix]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem liftProjection_embedding : liftProjection * restrictionEmbedding = 0 := by
  rw [← adaptedBasis_image]
  change adaptedInverse.submatrix liftIndex id * adaptedBasis.submatrix id imageIndex = 0
  rw [inverse_basis_submatrix]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem imageProjection_mixed : imageProjection * mixedEmbedding = 0 := by
  rw [← adaptedBasis_homology]
  change adaptedInverse.submatrix imageIndex id * adaptedBasis.submatrix id homologyIndex = 0
  rw [inverse_basis_submatrix]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem homologyProjection_mixed : homologyProjection * mixedEmbedding = 1 := by
  rw [← adaptedBasis_homology]
  change adaptedInverse.submatrix homologyIndex id * adaptedBasis.submatrix id homologyIndex = 1
  rw [inverse_basis_submatrix]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem liftProjection_mixed : liftProjection * mixedEmbedding = 0 := by
  rw [← adaptedBasis_homology]
  change adaptedInverse.submatrix liftIndex id * adaptedBasis.submatrix id homologyIndex = 0
  rw [inverse_basis_submatrix]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem imageProjection_lifts : imageProjection * restrictionLifts = 0 := by
  rw [← adaptedBasis_lifts]
  change adaptedInverse.submatrix imageIndex id * adaptedBasis.submatrix id liftIndex = 0
  rw [inverse_basis_submatrix]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem homologyProjection_lifts : homologyProjection * restrictionLifts = 0 := by
  rw [← adaptedBasis_lifts]
  change adaptedInverse.submatrix homologyIndex id * adaptedBasis.submatrix id liftIndex = 0
  rw [inverse_basis_submatrix]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem liftProjection_lifts : liftProjection * restrictionLifts = 1 := by
  rw [← adaptedBasis_lifts]
  change adaptedInverse.submatrix liftIndex id * adaptedBasis.submatrix id liftIndex = 1
  rw [inverse_basis_submatrix]
  decide +kernel

private theorem split_mul (M N : BinaryMatrix) :
    M * N = M.submatrix id imageIndex * N.submatrix imageIndex id +
      M.submatrix id homologyIndex * N.submatrix homologyIndex id +
      M.submatrix id liftIndex * N.submatrix liftIndex id := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.submatrix_apply, id_eq]
  rw [Fin.sum_univ_add (a := 50) (b := 62)]
  rw [Fin.sum_univ_add (a := 12) (b := 50)]
  simpa only [imageIndex, homologyIndex, liftIndex, Fin.castAdd, Fin.natAdd, Fin.castLE,
    ← Nat.add_assoc, Nat.reduceAdd] using
    (add_assoc (∑ k : Fin 50, M i (imageIndex k) * N (imageIndex k) j)
      (∑ k : Fin 12, M i (homologyIndex k) * N (homologyIndex k) j)
      (∑ k : Fin 50, M i (liftIndex k) * N (liftIndex k) j)).symm

theorem coordinate_resolution :
    restrictionEmbedding * imageProjection + mixedEmbedding * homologyProjection +
      restrictionLifts * liftProjection = 1 := by
  rw [← adaptedBasis_image, ← adaptedBasis_homology, ← adaptedBasis_lifts]
  exact (split_mul adaptedBasis adaptedInverse).symm.trans adaptedBasis_mul_inverse

theorem matrix_resolution {n : Type*} (M : Matrix (Fin 112) n (ZMod 2)) :
    M = restrictionEmbedding * (imageProjection * M) +
      mixedEmbedding * (homologyProjection * M) + restrictionLifts * (liftProjection * M) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Matrix.add_mul, ← Matrix.add_mul, coordinate_resolution, Matrix.one_mul]


theorem displacementMatrix_sq : (matrixA - 1) * (matrixA - 1) = 0 := by
  have hn : -(1 : BinaryMatrix) = 1 := by ext i j; exact CharTwo.neg_eq _
  have hs (M : BinaryMatrix) : M + M = 0 := by ext i j; exact CharTwo.add_self_eq_zero _
  rw [sub_eq_add_neg, hn, add_mul, mul_add, mul_add, mul_one, one_mul, one_mul,
    matrixA_mul_self]
  rw [add_assoc, ← add_assoc matrixA, hs, zero_add, hs]

theorem displacement_embedding : (matrixA - 1) * restrictionEmbedding = 0 := by
  rw [← restrictionEmbedding_displacement, ← Matrix.mul_assoc, displacementMatrix_sq,
    Matrix.zero_mul]

theorem displacement_mixed : (matrixA - 1) * mixedEmbedding = 0 := by
  rw [Matrix.sub_mul, mixedEmbedding_fixed, Matrix.one_mul, sub_self]

/-- The full displacement is exactly the map from the third block to the first. -/
theorem displacement_factorization : matrixA - 1 = restrictionEmbedding * liftProjection := by
  calc
    _ = (matrixA - 1) * 1 := (Matrix.mul_one _).symm
    _ = (matrixA - 1) * (restrictionEmbedding * imageProjection +
        mixedEmbedding * homologyProjection + restrictionLifts * liftProjection) := by
      rw [coordinate_resolution]
    _ = _ := by
      rw [Matrix.mul_add, Matrix.mul_add]
      simp only [← Matrix.mul_assoc, displacement_embedding, displacement_mixed,
        restrictionEmbedding_displacement, Matrix.zero_mul, zero_add]

theorem liftProjection_eq_extraction_displacement :
    liftProjection = restrictionExtraction * (matrixA - 1) := by
  rw [displacement_factorization, ← Matrix.mul_assoc, restrictionExtraction_embedding,
    Matrix.one_mul]

theorem fixedVectors_iff_liftProjection (v : NaturalModule) :
    v ∈ fixedVectors ↔ liftProjection *ᵥ v = 0 := by
  have he : v ∈ fixedVectors ↔ (matrixA - 1) *ᵥ v = 0 := by
    change displacement v = 0 ↔ _
    simp only [displacement_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [he]
  constructor
  · intro h
    rw [liftProjection_eq_extraction_displacement, ← Matrix.mulVec_mulVec, h,
      Matrix.mulVec_zero]
  · intro h
    rw [displacement_factorization, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

/-- Agreement on all three blocks determines an ambient matrix. -/
theorem matrix_ext_of_columns {M T : BinaryMatrix}
    (hE : M * restrictionEmbedding = T * restrictionEmbedding)
    (hH : M * mixedEmbedding = T * mixedEmbedding)
    (hL : M * restrictionLifts = T * restrictionLifts) : M = T := by
  calc
    M = M * (restrictionEmbedding * imageProjection + mixedEmbedding * homologyProjection +
        restrictionLifts * liftProjection) := by rw [coordinate_resolution, Matrix.mul_one]
    _ = T * (restrictionEmbedding * imageProjection + mixedEmbedding * homologyProjection +
        restrictionLifts * liftProjection) := by
      simp only [Matrix.mul_add, ← Matrix.mul_assoc, hE, hH, hL]
    _ = T := by rw [coordinate_resolution, Matrix.mul_one]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem invariantForm_transpose : invariantFormᵀ = invariantForm := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem restrictionPairing_transpose : restrictionPairingᵀ = restrictionPairing := by
  decide +kernel

theorem form_embedding_factorization :
    invariantForm * restrictionEmbedding = liftProjectionᵀ * restrictionPairing := by
  rw [liftProjection_eq_extraction_displacement, restrictionPairing_factorization]

theorem embedding_form_embedding :
    restrictionEmbeddingᵀ * invariantForm * restrictionEmbedding = 0 := by
  rw [Matrix.mul_assoc, form_embedding_factorization, ← Matrix.mul_assoc,
    ← Matrix.transpose_mul, liftProjection_embedding, Matrix.transpose_zero, Matrix.zero_mul]

theorem mixed_form_embedding : mixedEmbeddingᵀ * invariantForm * restrictionEmbedding = 0 := by
  rw [Matrix.mul_assoc, form_embedding_factorization, ← Matrix.mul_assoc,
    ← Matrix.transpose_mul, liftProjection_mixed, Matrix.transpose_zero, Matrix.zero_mul]

theorem embedding_form_mixed : restrictionEmbeddingᵀ * invariantForm * mixedEmbedding = 0 := by
  have h := congrArg Matrix.transpose mixed_form_embedding
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, invariantForm_transpose,
    Matrix.transpose_zero, Matrix.mul_assoc] using h

theorem embedding_form_lifts :
    restrictionEmbeddingᵀ * invariantForm * restrictionLifts = restrictionPairing := by
  have h := congrArg Matrix.transpose restrictionPairing_identity
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, invariantForm_transpose,
    restrictionPairing_transpose, Matrix.mul_assoc] using h

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer
