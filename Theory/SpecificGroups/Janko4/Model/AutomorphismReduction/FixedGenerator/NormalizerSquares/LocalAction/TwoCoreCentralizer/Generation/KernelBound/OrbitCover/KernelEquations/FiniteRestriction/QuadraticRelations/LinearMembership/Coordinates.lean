module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.Packed

/-!
# The fixed mixed columns and the inverse restriction

The displayed H columns are fixed by A, and the displayed pairing inverse
multiplies J to the identity. Both finite claims are checked by rectangular
XOR products in the kernel. Intertwining and the identity C E = 1 show that
the restriction of g inverse is inverse to the restriction of g. Preservation
of the ambient form then identifies it with the J-adjoint.

These are coordinate and transport facts only. The concrete mixed-space and
125-generator membership certificates remain separate obligations. See
../source/README.md and Data.lean for the ATLAS conventions and provenance.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
namespace LinearMembership
open GeneratorCertificates

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem mixedEmbedding_fixed :
    matrixA * mixedEmbedding = mixedEmbedding := by
  change rectDecode 112 aRows * rectDecode 12 mixedEmbeddingRows =
    rectDecode 12 mixedEmbeddingRows
  apply rectProduct_eq
  decide +kernel

theorem mixedEmbedding_col_mem_fixed (j : Fin 12) :
    (fun i => mixedEmbedding i j) ∈ fixedVectors := by
  change displacement _ = 0
  rw [displacement_apply]
  apply sub_eq_zero.mpr
  have h := congrArg (fun M : Matrix (Fin 112) (Fin 12) (ZMod 2) =>
    M *ᵥ Pi.single j 1) mixedEmbedding_fixed
  rw [← Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h
  exact h

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem pairingInverse_mul_pairing :
    pairingInverse * restrictionPairing = 1 := by
  change rectDecode 50 pairingInverseRows * rectDecode 50 restrictionPairingRows = 1
  rw [← rectDecode_one 50]
  apply rectProduct_eq
  simp only [get_ofFn]
  decide +kernel

theorem restrictionMatrix_mul_inverse (g : BinaryMatrixˣ) (hker : KernelConditions g) :
    restrictionMatrix g * restrictionMatrix (g⁻¹ : BinaryMatrixˣ) = 1 := by
  calc
    _ = restrictionExtraction * (g : BinaryMatrix) *
        (restrictionEmbedding * restrictionMatrix (g⁻¹ : BinaryMatrixˣ)) := by
      simp only [restrictionMatrix, Matrix.mul_assoc]
    _ = restrictionExtraction * (g : BinaryMatrix) *
        (((g⁻¹ : BinaryMatrixˣ) : BinaryMatrix) * restrictionEmbedding) := by
      rw [← restrictionMatrix_intertwining g⁻¹ (kernelConditions_inv g hker)]
    _ = restrictionExtraction *
        ((g : BinaryMatrix) * ((g⁻¹ : BinaryMatrixˣ) : BinaryMatrix)) *
        restrictionEmbedding := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Units.mul_inv, Matrix.mul_one, restrictionExtraction_embedding]

theorem restrictionMatrix_inverse_mul (g : BinaryMatrixˣ) (hker : KernelConditions g) :
    restrictionMatrix (g⁻¹ : BinaryMatrixˣ) * restrictionMatrix g = 1 := by
  simpa only [inv_inv] using
    restrictionMatrix_mul_inverse g⁻¹ (kernelConditions_inv g hker)

theorem pairingAdjoint_restrictionMatrix (g : BinaryMatrixˣ) (hker : KernelConditions g)
    (hform : formPullback g invariantForm = invariantForm) :
    pairingAdjoint (restrictionMatrix g) = restrictionMatrix (g⁻¹ : BinaryMatrixˣ) := by
  unfold pairingAdjoint
  calc
    _ = (pairingInverse * (restrictionMatrix g)ᵀ * restrictionPairing) *
        (restrictionMatrix g * restrictionMatrix (g⁻¹ : BinaryMatrixˣ)) := by
      rw [restrictionMatrix_mul_inverse g hker, Matrix.mul_one]
    _ = pairingInverse *
        ((restrictionMatrix g)ᵀ * restrictionPairing * restrictionMatrix g) *
        restrictionMatrix (g⁻¹ : BinaryMatrixˣ) := by simp only [Matrix.mul_assoc]
    _ = pairingInverse * restrictionPairing *
        restrictionMatrix (g⁻¹ : BinaryMatrixˣ) := by
      rw [restrictionMatrix_pairing g hker hform]
    _ = _ := by rw [pairingInverse_mul_pairing, Matrix.one_mul]

end LinearMembership
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
