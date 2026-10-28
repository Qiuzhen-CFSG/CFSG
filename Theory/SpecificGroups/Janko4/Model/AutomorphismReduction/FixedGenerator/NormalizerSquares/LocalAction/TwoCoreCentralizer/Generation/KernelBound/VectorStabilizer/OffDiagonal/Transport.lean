module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Blocks
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.RadicalCertificate


/-!
# Off-diagonal constraints from actual exterior radicals

Write E,H,L for the certified adapted columns and suppose the restriction S
is the identity. For every actual radical-I form R, the pullback difference
gᵀ R g - R annihilates both E and H, hence the whole fixed space K. Its L,L
block is Dᵀ M + Mᵀ D, where M = Hᵀ R L. The supplied RadicalKUpperBound
therefore places this block in the actual thirteen-generator upper span.

The complete mixed-image certificate supplies a radical-I lift for every
published mixed generator. This uses setwise exterior preservation and the
certified radical-row factorization, without assuming pointwise fixation.
Separately, D = 0 and preservation of invariantForm imply Bᵀ J = 0, and the
checked inverse of J kills B.

The literal matrix conventions, source motivation and untrusted finite tests
are documented in ../source/README.md. This module proves the algebraic
transport to those tests; it contains no finite-kernel assumption.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.OffDiagonal
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership

attribute [local irreducible] restrictionEmbedding restrictionExtraction restrictionMatrix
  mixedEmbedding restrictionLifts invariantForm liftProjection imageProjection
  upperMiddleBlock upperRightBlock middleRightBlock mixedEvaluation

private theorem exterior_transpose {R : BinaryMatrix} (hR : R ∈ exteriorFormSpace) :
    Rᵀ = R := by
  induction hR using Submodule.span_induction with
  | mem R hR =>
    obtain ⟨i, rfl⟩ := hR
    exact decodeExteriorForm_transpose _
  | zero => exact Matrix.transpose_zero
  | add R T _ _ hR hT => rw [Matrix.transpose_add, hR, hT]
  | smul c R _ hR => rw [Matrix.transpose_smul, hR]

private theorem radical_embedding_zero {R : BinaryMatrix}
    (hR : R ∈ exteriorRadical displacementVectors) :
    restrictionEmbeddingᵀ * R = 0 := by
  ext a b
  have hu : restrictionEmbedding *ᵥ Pi.single a 1 ∈ displacementVectors := by
    refine ⟨restrictionLifts *ᵥ Pi.single a 1, ?_⟩
    calc
      displacement (restrictionLifts *ᵥ Pi.single a 1) =
          (matrixA - 1) *ᵥ (restrictionLifts *ᵥ Pi.single a 1) := by
        simp only [displacement_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
      _ = _ := by rw [Matrix.mulVec_mulVec, restrictionEmbedding_displacement]
  have hv := hR.2 _ hu (Pi.single b 1)
  rw [formValue, dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_single_one, single_dotProduct, one_mul] at hv
  exact hv

private theorem radical_mixed_rows {R : BinaryMatrix}
    (hR : R ∈ exteriorRadical displacementVectors) :
    mixedEmbeddingᵀ * R = mixedEvaluation R * liftProjection := by
  rw [radical_mixed_factorization R hR, liftProjection_eq_extraction_displacement,
    Matrix.mul_assoc]

private theorem radical_mixed_zero {R : BinaryMatrix}
    (hR : R ∈ exteriorRadical displacementVectors) :
    mixedEmbeddingᵀ * R * mixedEmbedding = 0 := by
  rw [radical_mixed_rows hR, Matrix.mul_assoc, liftProjection_mixed, Matrix.mul_zero]

private theorem liftProjection_action (g : BinaryMatrixˣ) (hker : KernelConditions g)
    (hS : restrictionMatrix g = 1) :
    liftProjection * (g : BinaryMatrix) = liftProjection := by
  have hc : (matrixA - 1) * (g : BinaryMatrix) = (g : BinaryMatrix) * (matrixA - 1) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hker.1]
  have he : (g : BinaryMatrix) * restrictionEmbedding = restrictionEmbedding := by
    rw [restrictionMatrix_intertwining g hker, hS, Matrix.mul_one]
  calc
    _ = restrictionExtraction * ((matrixA - 1) * (g : BinaryMatrix)) := by
      rw [liftProjection_eq_extraction_displacement, Matrix.mul_assoc]
    _ = restrictionExtraction * ((g : BinaryMatrix) * (matrixA - 1)) := by rw [hc]
    _ = liftProjection := by
      rw [displacement_factorization, ← Matrix.mul_assoc (g : BinaryMatrix), he,
        ← Matrix.mul_assoc, restrictionExtraction_embedding, Matrix.one_mul]

private theorem radical_fixed_of_rows {R : BinaryMatrix} (hext : R ∈ exteriorFormSpace)
    (hE : restrictionEmbeddingᵀ * R = 0) (hH : mixedEmbeddingᵀ * R = 0) :
    R ∈ exteriorRadical fixedVectors := by
  have hr : R = liftProjectionᵀ * (restrictionLiftsᵀ * R) := by
    calc
      R = (restrictionEmbedding * imageProjection + mixedEmbedding * homologyProjection +
          restrictionLifts * liftProjection)ᵀ * R := by
        rw [coordinate_resolution, Matrix.transpose_one, Matrix.one_mul]
      _ = _ := by
        simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.add_mul,
          Matrix.mul_assoc, hE, hH, Matrix.mul_zero, zero_add]
  refine ⟨hext, ?_⟩
  intro u hu v
  rw [formValue, hr, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, (fixedVectors_iff_liftProjection u).mp hu, zero_dotProduct]

/-- With S = 1, pullback differences of radical-I forms annihilate all of K. -/
theorem pullback_difference_mem_radical_fixed (g : BinaryMatrixˣ)
    (hker : KernelConditions g) (hext : g ∈ formStabilizer exteriorFormSpace)
    (hS : restrictionMatrix g = 1) {R : BinaryMatrix}
    (hR : R ∈ exteriorRadical displacementVectors) :
    formPullback g R - R ∈ exteriorRadical fixedVectors := by
  apply radical_fixed_of_rows (exteriorFormSpace.sub_mem ((hext R).mpr hR.1) hR.1)
  · have he : (g : BinaryMatrix) * restrictionEmbedding = restrictionEmbedding := by
      rw [restrictionMatrix_intertwining g hker, hS, Matrix.mul_one]
    rw [Matrix.mul_sub, formPullback]
    have ht := congrArg Matrix.transpose he
    simp only [Matrix.transpose_mul] at ht
    simp only [← Matrix.mul_assoc, ht, radical_embedding_zero hR, Matrix.zero_mul, sub_self]
  · rw [Matrix.mul_sub, formPullback]
    have ht := congrArg Matrix.transpose (action_mixed g hker)
    simp only [Matrix.transpose_mul, Matrix.transpose_add] at ht
    calc
      _ = ((upperMiddleBlock g)ᵀ * (restrictionEmbeddingᵀ * R) +
          mixedEmbeddingᵀ * R) * (g : BinaryMatrix) - mixedEmbeddingᵀ * R := by
        simp only [← Matrix.mul_assoc, ht, Matrix.add_mul]
      _ = 0 := by
        rw [radical_embedding_zero hR, Matrix.mul_zero, zero_add, radical_mixed_rows hR,
          Matrix.mul_assoc, liftProjection_action g hker hS, sub_self]

/-- The actual lift block of the difference is the linear mixed-form test. -/
theorem pullback_difference_lifts (g : BinaryMatrixˣ) (hker : KernelConditions g)
    (hS : restrictionMatrix g = 1) {R : BinaryMatrix}
    (hR : R ∈ exteriorRadical displacementVectors) :
    restrictionLiftsᵀ * (formPullback g R - R) * restrictionLifts =
      (middleRightBlock g)ᵀ * mixedEvaluation R + (mixedEvaluation R)ᵀ * middleRightBlock g := by
  have hRE : R * restrictionEmbedding = 0 := by
    have ht := congrArg Matrix.transpose (radical_embedding_zero hR)
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, exterior_transpose hR.1,
      Matrix.transpose_zero] using ht
  have hMH : mixedEmbeddingᵀ * R * mixedEmbedding = 0 := radical_mixed_zero hR
  have hML : mixedEmbeddingᵀ * R * restrictionLifts = mixedEvaluation R := by
    unfold mixedEvaluation
    rfl
  have hLM : restrictionLiftsᵀ * R * mixedEmbedding = (mixedEvaluation R)ᵀ := by
    rw [← hML, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      exterior_transpose hR.1, Matrix.mul_assoc]
  have hact := action_lifts g hker
  rw [hS, Matrix.mul_one] at hact
  calc
    _ = ((g : BinaryMatrix) * restrictionLifts)ᵀ * R *
        ((g : BinaryMatrix) * restrictionLifts) - restrictionLiftsᵀ * R * restrictionLifts := by
      simp only [formPullback, Matrix.mul_sub, Matrix.sub_mul, Matrix.transpose_mul,
        Matrix.mul_assoc]
    _ = _ := by
      rw [hact]
      simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.add_mul, Matrix.mul_add]
      have hee : R * (restrictionEmbedding * upperRightBlock g) = 0 := by
        rw [← Matrix.mul_assoc, hRE, Matrix.zero_mul]
      have heh : mixedEmbeddingᵀ * R * (mixedEmbedding * middleRightBlock g) = 0 := by
        rw [← Matrix.mul_assoc, hMH, Matrix.zero_mul]
      have hec : (middleRightBlock g)ᵀ * mixedEmbeddingᵀ * R *
          (mixedEmbedding * middleRightBlock g) = 0 := by
        rw [Matrix.mul_assoc (middleRightBlock g)ᵀ, Matrix.mul_assoc (middleRightBlock g)ᵀ,
          heh, Matrix.mul_zero]
      simp only [Matrix.mul_assoc] at hee hec
      simp only [Matrix.mul_assoc, hee, hec, Matrix.mul_zero, zero_add, add_zero]
      simp only [← Matrix.mul_assoc]
      rw [Matrix.mul_assoc (middleRightBlock g)ᵀ mixedEmbeddingᵀ R,
        Matrix.mul_assoc (middleRightBlock g)ᵀ _ restrictionLifts, hML, hLM]
      have hCE : (upperRightBlock g)ᵀ * restrictionEmbeddingᵀ * R = 0 := by
        rw [Matrix.mul_assoc, radical_embedding_zero hR, Matrix.mul_zero]
      simp only [hCE, Matrix.zero_mul, zero_add, add_sub_assoc, sub_self, add_zero]
      exact add_comm _ _

/-- Every published mixed generator supplies the required upper-span constraint. -/
theorem mixed_constraint (hrad : RadicalKUpperBound) (g : BinaryMatrixˣ)
    (hker : KernelConditions g) (hext : g ∈ formStabilizer exteriorFormSpace)
    (hS : restrictionMatrix g = 1) (i : Fin 40) :
    (middleRightBlock g)ᵀ * mixedGenerator i +
      (mixedGenerator i)ᵀ * middleRightBlock g ∈ radicalKUpperSpace := by
  have hm : mixedGenerator i ∈ mixedImageSpace := by
    rw [mixedImageSpace_eq_mixedSpace]
    exact Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨R, hR, hM⟩ := hm
  rw [← hM, ← pullback_difference_lifts g hker hS hR]
  exact hrad _ (pullback_difference_mem_radical_fixed g hker hext hS hR)

/-- The invariant pairing kills B once D vanishes. -/
theorem upperMiddle_zero_of_middleRight_zero (g : BinaryMatrixˣ)
    (hker : KernelConditions g) (hform : formPullback g invariantForm = invariantForm)
    (hS : restrictionMatrix g = 1) (hD : middleRightBlock g = 0) :
    upperMiddleBlock g = 0 := by
  have hL := action_lifts g hker
  rw [hD, hS, Matrix.mul_zero, add_zero, Matrix.mul_one] at hL
  have he : (upperMiddleBlock g)ᵀ * restrictionPairing = 0 := by
    have hh := congrArg (fun F => mixedEmbeddingᵀ * F * restrictionLifts) hform
    have hx : mixedEmbeddingᵀ * formPullback g invariantForm * restrictionLifts =
        (upperMiddleBlock g)ᵀ * restrictionPairing +
        mixedEmbeddingᵀ * invariantForm * restrictionLifts := by
      calc
        _ = ((g : BinaryMatrix) * mixedEmbedding)ᵀ * invariantForm *
            ((g : BinaryMatrix) * restrictionLifts) := by
          simp only [formPullback, Matrix.transpose_mul, Matrix.mul_assoc]
        _ = _ := by
          rw [action_mixed g hker, hL]
          simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.add_mul, Matrix.mul_add,
            ← Matrix.mul_assoc]
          have hEE := embedding_form_embedding
          have hHE := mixed_form_embedding
          have hEL := embedding_form_lifts
          simp only [Matrix.mul_assoc] at hEE hHE hEL
          simp only [Matrix.mul_assoc, hEE, hHE, hEL, Matrix.mul_zero,
            Matrix.zero_mul, zero_add, add_zero]
    rw [hx] at hh
    exact add_right_cancel (hh.trans (zero_add _).symm)
  have ht := congrArg Matrix.transpose he
  rw [Matrix.transpose_mul, restrictionPairing_transpose, Matrix.transpose_transpose,
    Matrix.transpose_zero] at ht
  have hi := congrArg (fun M : Matrix (Fin 50) (Fin 12) (ZMod 2) => pairingInverse * M) ht
  simpa only [← Matrix.mul_assoc, pairingInverse_mul_pairing, Matrix.one_mul,
    Matrix.mul_zero] using hi

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.OffDiagonal
