module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.RadicalCertificate.WitnessData

/-!
# Ambient coordinates for the radical witnesses

The auxiliary packed rows here decode to the existing displacement, mixed
columns and lift maps. The quotient rows are exactly C(A-1).
All finite equalities are checked by kernel reduction; see source/generate.py.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.RadicalCertificate
open GeneratorCertificates

set_option maxRecDepth 10000 in
theorem embeddingTranspose_decode :
    restrictionEmbeddingᵀ = rectDecode 112 embeddingTransposeRows := by
  change rectDecode 112 restrictionColumns = rectDecode 112 embeddingTransposeRows
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem mixedTranspose_decode :
    mixedEmbeddingᵀ = rectDecode 112 mixedTransposeRows := by
  apply rectDecode_transpose
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem lifts_decode : restrictionLifts = rectDecode 50 liftRows := by
  change (rectDecode 112 restrictionLiftColumns)ᵀ = rectDecode 50 liftRows
  apply rectDecode_transpose
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem displacement_decode : matrixA - 1 = rectDecode 112 displacementRows := by
  have h : ∀ i : Fin 112, aRows.get i ^^^ 2 ^ i.val = displacementRows.get i := by
    decide +kernel
  ext i j
  rw [Matrix.sub_apply, CharTwo.sub_eq_add]
  change bit (aRows.get i) j.val + (1 : BinaryMatrix) i j = _
  rw [← rectDecode_one 112]
  change bit (aRows.get i) j.val + bit ((Vector.ofFn (fun i : Fin 112 => 2 ^ i.val)).get i) j.val = _
  rw [get_ofFn, ← bit_xor, h]
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem quotient_decode :
    restrictionExtraction * (matrixA - 1) = rectDecode 112 quotientRows := by
  rw [displacement_decode]
  change rectDecode 112 restrictionDualRows * rectDecode 112 displacementRows = _
  apply rectProduct_eq
  decide +kernel

/-- Vanishing on the displayed displacement columns implies the actual
left-radical condition on im(A-1). -/
theorem mem_exteriorRadical_of_embedding {R : BinaryMatrix}
    (hext : R ∈ exteriorFormSpace) (hzero : restrictionEmbeddingᵀ * R = 0) :
    R ∈ exteriorRadical displacementVectors := by
  refine ⟨hext, ?_⟩
  rintro u ⟨v, rfl⟩ w
  have hd : displacement v =
      restrictionEmbedding *ᵥ (restrictionExtraction *ᵥ ((matrixA - 1) *ᵥ v)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      restrictionEmbedding_extraction_displacement]
    simp only [displacement_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [formValue, hd, dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec]
  simp only [Matrix.mulVec_mulVec, hzero, Matrix.zero_mulVec, dotProduct_zero]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.RadicalCertificate
