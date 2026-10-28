module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.RadicalK.Data

/-!
# Upper blocks of the thirteen ambient kernel forms

The published lifts are the first fifty standard basis columns. Their
pullback therefore reads the leading 50-by-50 submatrix of an ambient form.
Literal entry checks identify those submatrices, for the thirteen kernel
words, with the unchanged generators of radicalKUpperSpace.
Source and regeneration: source/README.md and ../source/README.md.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.RadicalK
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership
open OrbitCoverCoordinates.LinearMembership.RadicalCertificate GeneratorCertificates

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem lifts_selection :
    restrictionLifts = (1 : BinaryMatrix).submatrix id imageIndex := by
  decide +kernel

private theorem upperBlock_eq_submatrix (R : BinaryMatrix) :
    restrictionLiftsᵀ * R * restrictionLifts = R.submatrix imageIndex imageIndex := by
  rw [lifts_selection, Matrix.transpose_submatrix, Matrix.transpose_one]
  change (1 : BinaryMatrix).submatrix imageIndex (Equiv.refl _) * R *
    (1 : BinaryMatrix).submatrix (Equiv.refl _) imageIndex = _
  rw [Matrix.one_submatrix_mul imageIndex (Equiv.refl _) R,
    Matrix.mul_submatrix_one (Equiv.refl _) imageIndex]
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem upper_checks : ∀ i : Fin 13, ∀ j k : Fin 50,
    ((radicalKRows.get i).get j).testBit k.val =
      if imageIndex j < imageIndex k then
        (ambientWords.get i).testBit (exteriorIndex (imageIndex j) (imageIndex k))
      else if imageIndex k < imageIndex j then
        (ambientWords.get i).testBit (exteriorIndex (imageIndex k) (imageIndex j))
      else false := by
  decide +kernel

/-- The upper blocks coincide with the thirteen shared literal generators. -/
theorem kernelForm_upper (i : Fin 13) :
    restrictionLiftsᵀ * kernelForm i * restrictionLifts = radicalKGenerator i := by
  rw [upperBlock_eq_submatrix]
  ext j k
  change decodeExteriorForm (ambientWords.get i) (imageIndex j) (imageIndex k) =
    bit ((radicalKRows.get i).get j) k.val
  simp only [decodeExteriorForm, bit, upper_checks]
  by_cases hjk : imageIndex j < imageIndex k <;>
    by_cases hkj : imageIndex k < imageIndex j <;> simp [hjk, hkj]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.RadicalK
