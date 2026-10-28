module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.Coordinates

/-!
# Transport from homology to the mixed right-stabilizer

For a radical-I exterior form R, the homology kernel makes the mixed rows
of its pullback equal the H rows of R g. If every such row factors through
C(A-1), multiplying by L gives (Hᵀ R L) S with S = C g E. Thus the actual
mixed image is stable under right multiplication by S. Once this image is
identified with the displayed mixedSpace, the same argument for the inverse
and the pairing identity give the corresponding constraint for the J-adjoint.

The radical-row factorization and the concrete image identification are
explicit finite premises here. This module does not assume pointwise
fixation of radical forms, chart quadrics, or local group identification.
Their certification belongs to the finite calculation documented in
../source/README.md and Data.lean, using the unchanged ATLAS columns.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership

private theorem mixedRow_mulVec (R : BinaryMatrix) (v : NaturalModule) (i : Fin 12) :
    ((mixedEmbeddingᵀ * R) *ᵥ v) i =
      formValue R (fun k => mixedEmbedding k i) v := by
  rw [← Matrix.mulVec_mulVec]
  rfl

/-- The mixed evaluations supplied by the homology condition determine the
whole matrix of rows indexed by the fixed H columns. -/
theorem mixed_rows_transport (g : BinaryMatrixˣ) (hmix : MixedFormConditions g)
    {R : BinaryMatrix} (hR : R ∈ exteriorRadical displacementVectors) :
    ∃ T ∈ exteriorRadical displacementVectors,
      mixedEmbeddingᵀ * T = mixedEmbeddingᵀ * R * (g : BinaryMatrix) := by
  obtain ⟨T, hT, h⟩ := hmix R hR
  refine ⟨T, hT, ?_⟩
  ext i j
  have hij := h (fun k => mixedEmbedding k i) (mixedEmbedding_col_mem_fixed i)
    (Pi.single j 1)
  rw [← mixedRow_mulVec, ← mixedRow_mulVec, Matrix.mulVec_mulVec] at hij
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hij

/-- C N reads the induced quotient action on the chosen lifts. -/
theorem extraction_displacement_action (g : BinaryMatrixˣ) (hker : KernelConditions g) :
    restrictionExtraction * (matrixA - 1) * (g : BinaryMatrix) * restrictionLifts =
      restrictionMatrix g := by
  have hc : (g : BinaryMatrix) * (matrixA - 1) =
      (matrixA - 1) * (g : BinaryMatrix) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hker.1]
  calc
    _ = restrictionExtraction * ((matrixA - 1) * (g : BinaryMatrix)) *
        restrictionLifts := by simp only [Matrix.mul_assoc]
    _ = restrictionExtraction * ((g : BinaryMatrix) * (matrixA - 1)) *
        restrictionLifts := by rw [hc]
    _ = restrictionExtraction * (g : BinaryMatrix) *
        ((matrixA - 1) * restrictionLifts) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [restrictionEmbedding_displacement]; rfl

/-- A factorization of the radical rows makes right multiplication on the
actual mixed image a consequence of the homology condition. This hypothesis
is a finite identity about the fixed exterior space, not an invariance
assumption on the unknown matrix. -/
theorem restrictionMatrix_preserves_mixedImage (g : BinaryMatrixˣ)
    (hker : KernelConditions g) (hmix : MixedFormConditions g)
    (hfactor : ∀ R ∈ exteriorRadical displacementVectors,
      mixedEmbeddingᵀ * R =
        mixedEvaluation R * restrictionExtraction * (matrixA - 1)) :
    ∀ M ∈ mixedImageSpace, M * restrictionMatrix g ∈ mixedImageSpace := by
  rintro M ⟨R, hR, rfl⟩
  obtain ⟨T, hT, hrows⟩ := mixed_rows_transport g hmix hR
  refine ⟨T, hT, ?_⟩
  change mixedEmbeddingᵀ * T * restrictionLifts = _
  rw [hrows, hfactor R hR]
  calc
    _ = mixedEvaluation R *
        (restrictionExtraction * (matrixA - 1) * (g : BinaryMatrix) *
          restrictionLifts) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [extraction_displacement_action g hker]

/-- Once the two concrete mixed-space facts are certified, the exterior
hypothesis supplies the right-stabilizer condition. -/
theorem restrictionMatrix_preservesMixedSpace (g : BinaryMatrixˣ)
    (hker : KernelConditions g) (hext : g ∈ formStabilizer exteriorFormSpace)
    (himage : mixedImageSpace = mixedSpace)
    (hfactor : ∀ R ∈ exteriorRadical displacementVectors,
      mixedEmbeddingᵀ * R =
        mixedEvaluation R * restrictionExtraction * (matrixA - 1)) :
    PreservesMixedSpace (restrictionMatrix g) := by
  intro M hM
  rw [← himage] at hM ⊢
  exact restrictionMatrix_preserves_mixedImage g hker
    (mixedFormConditions_of_kernel g hker hext) hfactor M hM

/-- Applying the same restriction to the inverse produces the independent
adjoint condition. No pointwise fixation of radical forms is used. -/
theorem restrictionMatrix_mixed_constraints (g : BinaryMatrixˣ)
    (hker : KernelConditions g)
    (hform : formPullback g invariantForm = invariantForm)
    (hext : g ∈ formStabilizer exteriorFormSpace)
    (himage : mixedImageSpace = mixedSpace)
    (hfactor : ∀ R ∈ exteriorRadical displacementVectors,
      mixedEmbeddingᵀ * R =
        mixedEvaluation R * restrictionExtraction * (matrixA - 1)) :
    PreservesMixedSpace (restrictionMatrix g) ∧
      PreservesMixedSpace (pairingAdjoint (restrictionMatrix g)) := by
  constructor
  · exact restrictionMatrix_preservesMixedSpace g hker hext himage hfactor
  · rw [pairingAdjoint_restrictionMatrix g hker hform]
    exact restrictionMatrix_preservesMixedSpace g⁻¹ (kernelConditions_inv g hker)
      ((formStabilizer exteriorFormSpace).inv_mem hext) himage hfactor

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership
