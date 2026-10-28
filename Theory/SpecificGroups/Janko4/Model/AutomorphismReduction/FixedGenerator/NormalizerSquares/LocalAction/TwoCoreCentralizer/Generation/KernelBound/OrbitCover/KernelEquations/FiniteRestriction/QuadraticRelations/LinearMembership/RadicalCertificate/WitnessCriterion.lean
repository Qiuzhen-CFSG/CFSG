module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.RadicalCertificate.AmbientCoordinates

/-!
# Soundness of the radical witness checks

The numerical contract checks an exterior linear combination, its full ambient
matrix, its zero displacement rows, its H rows, its mixed image and its row
factorization. No dimension or completeness assertion is assumed here.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.RadicalCertificate
open GeneratorCertificates

def WitnessChecks (i : Fin 53) : Prop :=
  scan (radicalCoefficients.get i) exteriorFormRows.toList = radicalFormWords.get i ∧
  (∀ j k : Fin 112, ((radicalRows.get i).get j).testBit k.val =
    if j < k then (radicalFormWords.get i).testBit (exteriorIndex j k)
    else if k < j then (radicalFormWords.get i).testBit (exteriorIndex k j) else false) ∧
  (∀ j : Fin 50, scan (embeddingTransposeRows.get j) (radicalRows.get i).toList = 0) ∧
  (∀ j : Fin 12, scan (mixedTransposeRows.get j) (radicalRows.get i).toList =
    (radicalHRows.get i).get j) ∧
  (∀ j : Fin 12, scan ((radicalHRows.get i).get j) liftRows.toList =
    (radicalMixedRows.get i).get j) ∧
  (∀ j : Fin 12, scan ((radicalMixedRows.get i).get j) quotientRows.toList =
    (radicalHRows.get i).get j)

theorem witness_sound (i : Fin 53) (h : WitnessChecks i) :
    radicalGenerator i ∈ exteriorRadical displacementVectors ∧
    mixedEvaluation (radicalGenerator i) = rectDecode 50 (radicalMixedRows.get i) ∧
    mixedEmbeddingᵀ * radicalGenerator i =
      mixedEvaluation (radicalGenerator i) * restrictionExtraction * (matrixA - 1) := by
  obtain ⟨hc, hr, hz, hh, hm, hf⟩ := h
  have hext : radicalGenerator i ∈ exteriorFormSpace := by
    rw [radicalGenerator, ← hc, scan_eq, decodeExteriorForm_combination]
    exact exteriorFormSpace.sum_mem (fun j _ =>
      exteriorFormSpace.smul_mem _ (exteriorBasisForm_mem j))
  have hrows : rectDecode 112 (radicalRows.get i) = radicalGenerator i :=
    rectDecode_eq_exterior _ _ hr
  have hzero : restrictionEmbeddingᵀ * radicalGenerator i = 0 := by
    rw [embeddingTranspose_decode, ← hrows]
    apply rectProduct_zero
    simpa only [scan_eq] using hz
  have hH : mixedEmbeddingᵀ * radicalGenerator i =
      rectDecode 112 (radicalHRows.get i) := by
    rw [mixedTranspose_decode, ← hrows]
    apply rectProduct_eq
    simpa only [scan_eq] using hh
  have hM : mixedEvaluation (radicalGenerator i) =
      rectDecode 50 (radicalMixedRows.get i) := by
    change mixedEmbeddingᵀ * radicalGenerator i * restrictionLifts = _
    rw [hH, lifts_decode]
    apply rectProduct_eq
    simpa only [scan_eq] using hm
  refine ⟨mem_exteriorRadical_of_embedding hext hzero, hM, ?_⟩
  rw [hH, hM, Matrix.mul_assoc, quotient_decode]
  symm
  apply rectProduct_eq
  simpa only [scan_eq] using hf

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.RadicalCertificate

