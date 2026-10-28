module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Blocks

/-!
# Pullback identities for the final shear
The certified E,H,L basis reduces the remaining element to 1 + E C Q.
Preservation of the invariant form makes J C symmetric. For a symmetric
exterior form vanishing on I-by-K, its pullback difference annihilates K
and has upper block Cᵀ L_R + L_Rᵀ C. The finite tests use these identities
without identifying the exterior stabilizer with the generated group.
Source and witness conventions: ../source/README.md.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership

attribute [local irreducible] restrictionEmbedding restrictionExtraction restrictionMatrix
  restrictionLifts mixedEmbedding invariantForm restrictionPairing pairingInverse
  upperRightBlock upperMiddleBlock middleRightBlock imageProjection homologyProjection liftProjection

theorem shear_action_lifts (g : BinaryMatrixˣ) (hker : KernelConditions g)
    (hS : restrictionMatrix g = 1) (hD : middleRightBlock g = 0) :
    (g : BinaryMatrix) * restrictionLifts =
      restrictionEmbedding * upperRightBlock g + restrictionLifts := by
  rw [action_lifts g hker, hS, hD, Matrix.mul_zero, add_zero, Matrix.mul_one]

theorem shear_matrix (g : BinaryMatrixˣ) (hker : KernelConditions g)
    (hS : restrictionMatrix g = 1) (hD : middleRightBlock g = 0)
    (hB : upperMiddleBlock g = 0) :
    (g : BinaryMatrix) =
      1 + restrictionEmbedding * upperRightBlock g * liftProjection := by
  apply matrix_ext_of_columns
  · rw [restrictionMatrix_intertwining g hker, hS, Matrix.mul_one]
    simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc,
      liftProjection_embedding, Matrix.mul_zero, add_zero]
  · rw [action_mixed g hker, hB, Matrix.mul_zero, zero_add]
    simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc,
      liftProjection_mixed, Matrix.mul_zero, add_zero]
  · rw [shear_action_lifts g hker hS hD]
    simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc,
      liftProjection_lifts, Matrix.mul_one]
    exact add_comm _ _

theorem shear_pullback_lifts (g : BinaryMatrixˣ) (hker : KernelConditions g)
    (hS : restrictionMatrix g = 1) (hD : middleRightBlock g = 0)
    (R : BinaryMatrix) (hRt : Rᵀ = R)
    (hEE : restrictionEmbeddingᵀ * R * restrictionEmbedding = 0) :
    restrictionLiftsᵀ * (formPullback g R - R) * restrictionLifts =
      (upperRightBlock g)ᵀ * (restrictionEmbeddingᵀ * R * restrictionLifts) +
      (restrictionEmbeddingᵀ * R * restrictionLifts)ᵀ * upperRightBlock g := by
  have hp : restrictionLiftsᵀ * formPullback g R * restrictionLifts =
      ((g : BinaryMatrix) * restrictionLifts)ᵀ * R *
        ((g : BinaryMatrix) * restrictionLifts) := by
    simp only [formPullback, Matrix.transpose_mul, Matrix.mul_assoc]
  have hz : (restrictionEmbedding * upperRightBlock g)ᵀ * R *
      (restrictionEmbedding * upperRightBlock g) = 0 := by
    calc
      _ = (upperRightBlock g)ᵀ *
          (restrictionEmbeddingᵀ * R * restrictionEmbedding) * upperRightBlock g := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hEE, Matrix.mul_zero, Matrix.zero_mul]
  rw [Matrix.mul_sub, Matrix.sub_mul, hp, shear_action_lifts g hker hS hD,
    Matrix.transpose_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_add, hz, zero_add]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hRt, Matrix.mul_assoc]
  abel

private theorem transpose_eq_of_add_eq_zero (M : RestrictionMatrix)
    (h : Mᵀ + M = 0) : Mᵀ = M := by
  apply Matrix.ext
  intro i j
  apply (CharTwo.add_eq_zero (a := M j i) (b := M i j)).mp
  exact congrArg (fun X : RestrictionMatrix => X i j) h

theorem shear_pairing_symmetric (g : BinaryMatrixˣ) (hker : KernelConditions g)
    (hform : formPullback g invariantForm = invariantForm)
    (hS : restrictionMatrix g = 1) (hD : middleRightBlock g = 0) :
    (restrictionPairing * upperRightBlock g)ᵀ =
      restrictionPairing * upperRightBlock g := by
  have h := shear_pullback_lifts g hker hS hD invariantForm
    invariantForm_transpose embedding_form_embedding
  rw [hform, sub_self, Matrix.mul_zero, Matrix.zero_mul, embedding_form_lifts,
    restrictionPairing_transpose] at h
  have ht : (restrictionPairing * upperRightBlock g)ᵀ +
      restrictionPairing * upperRightBlock g = 0 := by
    simpa only [Matrix.transpose_mul, restrictionPairing_transpose] using h.symm
  exact transpose_eq_of_add_eq_zero _ ht

private theorem fixed_columns_pullback_difference {n : Type*} [Fintype n]
    (g : BinaryMatrixˣ) (C : RestrictionMatrix)
    (hg : (g : BinaryMatrix) = 1 + restrictionEmbedding * C * liftProjection)
    (X : Matrix (Fin 112) n (ZMod 2)) (hX : (g : BinaryMatrix) * X = X)
    (R : BinaryMatrix) (hz : Xᵀ * R * restrictionEmbedding = 0) :
    Xᵀ * (formPullback g R - R) = 0 := by
  have hp : Xᵀ * formPullback g R = ((g : BinaryMatrix) * X)ᵀ * R *
      (g : BinaryMatrix) := by
    simp only [formPullback, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [Matrix.mul_sub, hp, hX, hg, Matrix.mul_add, Matrix.mul_one]
  have hzero : Xᵀ * R * (restrictionEmbedding * C * liftProjection) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hz, Matrix.zero_mul, Matrix.zero_mul]
  rw [hzero, add_zero, sub_self]

theorem mem_exteriorRadical_fixed_of_columns (R : BinaryMatrix)
    (hR : R ∈ exteriorFormSpace)
    (hE : restrictionEmbeddingᵀ * R = 0) (hH : mixedEmbeddingᵀ * R = 0) :
    R ∈ exteriorRadical fixedVectors := by
  refine ⟨hR, ?_⟩
  intro u hu v
  have hQ := (fixedVectors_iff_liftProjection u).mp hu
  have hu' : u = restrictionEmbedding *ᵥ (imageProjection *ᵥ u) +
      mixedEmbedding *ᵥ (homologyProjection *ᵥ u) := by
    have h := congrArg (fun M : BinaryMatrix => M *ᵥ u) coordinate_resolution
    simpa only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hQ, Matrix.mulVec_zero,
      add_zero, Matrix.one_mulVec] using h.symm
  rw [formValue, hu', add_dotProduct]
  have hzero {n : Type} [Fintype n] (X : Matrix (Fin 112) n (ZMod 2))
      (hX : Xᵀ * R = 0) (w : n → ZMod 2) :
      (X *ᵥ w) ⬝ᵥ (R *ᵥ v) = 0 := by
    rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec,
      Matrix.mulVec_mulVec, hX, Matrix.zero_mulVec, dotProduct_zero]
  rw [hzero restrictionEmbedding hE (imageProjection *ᵥ u),
    hzero mixedEmbedding hH (homologyProjection *ᵥ u), add_zero]

theorem shear_pullback_difference_radical (g : BinaryMatrixˣ) (hker : KernelConditions g)
    (hext : g ∈ formStabilizer exteriorFormSpace)
    (hS : restrictionMatrix g = 1) (hD : middleRightBlock g = 0)
    (hB : upperMiddleBlock g = 0)
    (R : BinaryMatrix) (hR : R ∈ exteriorFormSpace) (hRt : Rᵀ = R)
    (hEE : restrictionEmbeddingᵀ * R * restrictionEmbedding = 0)
    (hEH : restrictionEmbeddingᵀ * R * mixedEmbedding = 0) :
    formPullback g R - R ∈ exteriorRadical fixedVectors := by
  apply mem_exteriorRadical_fixed_of_columns
  · exact exteriorFormSpace.sub_mem ((hext R).mpr hR) hR
  · apply fixed_columns_pullback_difference g _ (shear_matrix g hker hS hD hB)
    · rw [restrictionMatrix_intertwining g hker, hS, Matrix.mul_one]
    · exact hEE
  · apply fixed_columns_pullback_difference g _ (shear_matrix g hker hS hD hB)
    · rw [action_mixed g hker, hB, Matrix.mul_zero, zero_add]
    · have h := congrArg Matrix.transpose hEH
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hRt,
        Matrix.transpose_zero, Matrix.mul_assoc] using h

theorem shear_test_mem_upper (hrad : RadicalKUpperBound)
    (g : BinaryMatrixˣ) (hker : KernelConditions g)
    (hext : g ∈ formStabilizer exteriorFormSpace)
    (hS : restrictionMatrix g = 1) (hD : middleRightBlock g = 0)
    (hB : upperMiddleBlock g = 0)
    (R : BinaryMatrix) (hR : R ∈ exteriorFormSpace) (hRt : Rᵀ = R)
    (hEE : restrictionEmbeddingᵀ * R * restrictionEmbedding = 0)
    (hEH : restrictionEmbeddingᵀ * R * mixedEmbedding = 0) :
    (upperRightBlock g)ᵀ * (restrictionEmbeddingᵀ * R * restrictionLifts) +
      (restrictionEmbeddingᵀ * R * restrictionLifts)ᵀ * upperRightBlock g ∈
        radicalKUpperSpace := by
  have h := hrad _ (shear_pullback_difference_radical g hker hext hS hD hB
    R hR hRt hEE hEH)
  rwa [shear_pullback_lifts g hker hS hD R hRt hEE] at h

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer
