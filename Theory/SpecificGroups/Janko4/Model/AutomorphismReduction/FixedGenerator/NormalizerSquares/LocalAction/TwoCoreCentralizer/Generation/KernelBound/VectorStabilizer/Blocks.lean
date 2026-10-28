module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Coordinates

/-!
# The full adapted matrix of a homology-kernel element

The kernel condition makes the action on fixed columns trivial modulo the
image of A - 1. In the certified E,H,L basis this gives [S B C; 0 1 D; 0 0 S],
with S exactly the published restrictionMatrix. The three column identities
below prove this for every matrix unit satisfying KernelConditions.

Once all blocks are determined, the final equality test yields 1 or A in
the original 112-dimensional module. The statements require no local subgroup,
order, simplicity, or identification of an ambient form stabilizer with J4.
The ATLAS conventions and source motivation are in source/README.md.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership

attribute [local irreducible] restrictionEmbedding restrictionExtraction restrictionMatrix

/-- A kernel element changes a fixed vector only by an image column. -/
theorem fixed_shift_projection (g : BinaryMatrixˣ) (hker : KernelConditions g)
    (v : NaturalModule) (hv : matrixA *ᵥ v = v) :
    restrictionEmbedding *ᵥ (imageProjection *ᵥ ((g : BinaryMatrix) *ᵥ v - v)) =
      (g : BinaryMatrix) *ᵥ v - v := by
  obtain ⟨w, hw⟩ := hker.2 v hv
  have hw' : (g : BinaryMatrix) *ᵥ v - v =
      restrictionEmbedding *ᵥ (liftProjection *ᵥ w) := by
    rw [Matrix.mulVec_mulVec, ← displacement_factorization]
    simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using hw
  rw [hw', Matrix.mulVec_mulVec _ imageProjection restrictionEmbedding,
    imageProjection_embedding, Matrix.one_mulVec]

/-- The actual middle columns have diagonal block one and lower block zero. -/
theorem action_mixed (g : BinaryMatrixˣ) (hker : KernelConditions g) :
    (g : BinaryMatrix) * mixedEmbedding =
      restrictionEmbedding * upperMiddleBlock g + mixedEmbedding := by
  apply sub_eq_iff_eq_add.mp
  calc
    (g : BinaryMatrix) * mixedEmbedding - mixedEmbedding =
        restrictionEmbedding * (imageProjection *
          ((g : BinaryMatrix) * mixedEmbedding - mixedEmbedding)) := by
      apply Matrix.ext_of_mulVec_single
      intro j
      have hv : matrixA *ᵥ (mixedEmbedding *ᵥ Pi.single j 1) =
          mixedEmbedding *ᵥ Pi.single j 1 := by
        rw [Matrix.mulVec_mulVec, mixedEmbedding_fixed]
      have hp := fixed_shift_projection g hker _ hv
      have hs : (g : BinaryMatrix) *ᵥ (mixedEmbedding *ᵥ Pi.single j 1) -
          mixedEmbedding *ᵥ Pi.single j 1 =
          ((g : BinaryMatrix) * mixedEmbedding - mixedEmbedding) *ᵥ Pi.single j 1 := by
        rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
      rw [hs] at hp
      have hp' : (restrictionEmbedding * (imageProjection *
          ((g : BinaryMatrix) * mixedEmbedding - mixedEmbedding))) *ᵥ Pi.single j 1 =
          ((g : BinaryMatrix) * mixedEmbedding - mixedEmbedding) *ᵥ Pi.single j 1 := by
        simpa only [← Matrix.mulVec_mulVec] using hp
      exact hp'.symm
    _ = restrictionEmbedding * upperMiddleBlock g := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, imageProjection_mixed, sub_zero]
      rfl

/-- Commutation with A identifies the lower-right block with the restriction S. -/
theorem liftProjection_action_lifts (g : BinaryMatrixˣ) (hker : KernelConditions g) :
    liftProjection * (g : BinaryMatrix) * restrictionLifts = restrictionMatrix g := by
  have hc : (matrixA - 1) * (g : BinaryMatrix) = (g : BinaryMatrix) * (matrixA - 1) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hker.1]
  rw [liftProjection_eq_extraction_displacement]
  calc
    _ = restrictionExtraction * ((matrixA - 1) * (g : BinaryMatrix)) * restrictionLifts := by
      simp only [Matrix.mul_assoc]
    _ = restrictionExtraction * ((g : BinaryMatrix) * (matrixA - 1)) * restrictionLifts := by
      rw [hc]
    _ = restrictionExtraction * (g : BinaryMatrix) * ((matrixA - 1) * restrictionLifts) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [restrictionEmbedding_displacement]; unfold restrictionMatrix; rfl

/-- Together with intertwining and action_mixed, this is the full block form
[S B C; 0 1 D; 0 0 S], in the certified E,H,L basis. -/
theorem action_lifts (g : BinaryMatrixˣ) (hker : KernelConditions g) :
    (g : BinaryMatrix) * restrictionLifts =
      restrictionEmbedding * upperRightBlock g + mixedEmbedding * middleRightBlock g +
        restrictionLifts * restrictionMatrix g := by
  have h := matrix_resolution ((g : BinaryMatrix) * restrictionLifts)
  simpa only [← Matrix.mul_assoc, liftProjection_action_lifts g hker,
    upperRightBlock, middleRightBlock] using h

/-- Determining every block proves equality in the original 112-dimensional
matrix group. Restriction to the displacement space alone is not used as
an equality test. -/
theorem eq_one_or_matrixUnitA_of_blocks (g : BinaryMatrixˣ) (hker : KernelConditions g)
    (hS : restrictionMatrix g = 1) (hB : upperMiddleBlock g = 0)
    (hD : middleRightBlock g = 0) (hC : upperRightBlock g = 0 ∨ upperRightBlock g = 1) :
    g = 1 ∨ g = matrixUnitA := by
  have hE : (g : BinaryMatrix) * restrictionEmbedding = restrictionEmbedding := by
    rw [restrictionMatrix_intertwining g hker, hS, Matrix.mul_one]
  have hH : (g : BinaryMatrix) * mixedEmbedding = mixedEmbedding := by
    rw [action_mixed g hker, hB, Matrix.mul_zero, zero_add]
  have hL := action_lifts g hker
  rw [hD, hS, Matrix.mul_zero, add_zero, Matrix.mul_one] at hL
  rcases hC with hC | hC
  · left
    apply Units.ext
    apply matrix_ext_of_columns
    · simpa only [Units.val_one, Matrix.one_mul] using hE
    · simpa only [Units.val_one, Matrix.one_mul] using hH
    · simpa only [Units.val_one, hC, Matrix.mul_zero, zero_add, Matrix.one_mul] using hL
  · right
    apply Units.ext
    change (g : BinaryMatrix) = matrixA
    apply matrix_ext_of_columns
    · have ha := displacement_embedding
      rw [Matrix.sub_mul, Matrix.one_mul] at ha
      exact hE.trans (sub_eq_zero.mp ha).symm
    · exact hH.trans mixedEmbedding_fixed.symm
    · have ha := restrictionEmbedding_displacement
      rw [Matrix.sub_mul, Matrix.one_mul] at ha
      rw [hC, Matrix.mul_one] at hL
      exact hL.trans (sub_eq_iff_eq_add.mp ha).symm

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer
