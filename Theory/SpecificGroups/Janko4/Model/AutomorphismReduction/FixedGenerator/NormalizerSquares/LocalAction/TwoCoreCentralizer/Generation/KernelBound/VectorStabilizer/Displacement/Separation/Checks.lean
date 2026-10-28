module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Displacement.Separation.Arithmetic
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Displacement.Separation.Witnesses

/-! Kernel checks for the nine-space, original test form, and full coefficient
recovery. No numerical dimension or Python calculation is trusted.
Source and regeneration: source/generate.py. -/

public section
set_option Elab.async false
set_option maxRecDepth 10000
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Displacement.Separation
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership
open GeneratorCertificates LinearMembership.FiniteAlgebra
open PolynomialCertificate

set_option maxHeartbeats 5000000 in
theorem factor_checks : ∀ k : Fin 45, ∀ i : Fin 50,
    scan (selfAdjointImageRows.get i) (factorRows.get k).toList =
      (selfAdjointWords.get k >>> (50*i.val)) % 2^50 := by decide +kernel

set_option maxHeartbeats 5000000 in
theorem image_transpose_checks : ∀ i : Fin 50, ∀ j : Fin 9,
    (selfAdjointImageRows.get i).testBit j.val =
      (imageTransposeRows.get j).testBit i.val := by decide +kernel

set_option maxHeartbeats 5000000 in
theorem form_image_checks : ∀ i : Fin 50,
    scan (testFormRows.get i) selfAdjointImageRows.toList = formImageRows.get i := by
  decide +kernel

set_option maxHeartbeats 5000000 in
theorem image_isotropic_checks : ∀ i : Fin 9,
    scan (imageTransposeRows.get i) formImageRows.toList = 0 := by decide +kernel

set_option maxHeartbeats 5000000 in
theorem form_symmetric_checks : ∀ i j : Fin 50,
    (testFormRows.get i).testBit j.val = (testFormRows.get j).testBit i.val := by
  decide +kernel

set_option maxHeartbeats 5000000 in
theorem ambient_combination_check :
    ambientWord = ExteriorInvariance.combination testOriginalCoefficients := by decide +kernel

set_option maxHeartbeats 5000000 in
theorem ambient_rows_check : ∀ i : Fin 112,
    ambientRows.get i = (ambientWord >>> (112*i.val)) % 2^112 := by decide +kernel

set_option maxHeartbeats 5000000 in
theorem ambient_left_checks : ∀ i : Fin 50,
    scan (restrictionColumns.get i) ambientRows.toList = ambientLeftRows.get i := by
  decide +kernel

set_option maxHeartbeats 5000000 in
theorem ambient_restriction_checks : ∀ i : Fin 50,
    scan (ambientLeftRows.get i) ExteriorAnnihilators.embeddingRows.toList =
      testFormRows.get i := by decide +kernel

set_option maxHeartbeats 5000000 in
theorem product_checks : ∀ k : Fin 45, ∀ i : Fin 50,
    scan (testFormRows.get i) (slices 50 50 (selfAdjointWords.get k)).toList =
      (productWords.get k >>> (50*i.val)) % 2^50 := by
  simp only [slices, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
theorem effect_checks : ∀ k : Fin 45, ∀ i j : Fin 50,
    (effectWords.get k).testBit (j.val + 50*i.val) =
      ((productWords.get k).testBit (j.val + 50*i.val) ^^
        (productWords.get k).testBit (i.val + 50*j.val)) := by decide +kernel

set_option maxHeartbeats 5000000 in
theorem weight_checks : ∀ k : Fin 45, ∀ i : Fin 50,
    (weightWords.get k >>> (50*i.val)) % 2^50 =
      PullbackCoefficients.weightRow
        (ExteriorAnnihilators.weights.get (selectedWeights.get k)) i % 2^50 := by decide +kernel

set_option maxHeartbeats 5000000 in
theorem evaluation_checks : ∀ i k : Fin 45,
    (packedDot 2500 12 (weightWords.get i) (effectWords.get k)).testBit 0 =
      (evaluationRows.get i).testBit k.val := by decide +kernel

set_option maxHeartbeats 5000000 in
/-- Each individual coefficient is recovered from complete evaluation rows. -/
theorem recovery_checks : ∀ i : Fin 45,
    scan (recoveryRows.get i) evaluationRows.toList = 2^i.val := by decide +kernel

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Displacement.Separation
