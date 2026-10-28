module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.RadicalCertificate.CompletenessReduction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.RadicalCertificate.CoefficientKernel
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.RadicalCertificate.EvaluationCertificate

/-!
# The complete mixed radical certificates

The 53 displayed forms span the actual exterior radical. Correctness of the
selected-evaluation coefficient table and reconstruction of its kernel prove
the converse to witness membership. Their mixed images span exactly mixedSpace,
and their H rows satisfy the required factorization. Linearity therefore gives
both certificates for every actual radical form.

The conditional assembly interfaces are retained, and the final theorems
discharge both finite premises. See RadicalCertificate/source/README.md and
source/README.md for the exact contracts and the unchanged ATLAS conventions.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership
open RadicalCertificate

/-- Every displayed mixed generator is the evaluation of a genuine radical form. -/
theorem mixedSpace_le_mixedImageSpace : mixedSpace ≤ mixedImageSpace := by
  rw [← radicalSpan_mixed_image]
  exact Submodule.map_mono radicalSpan_le

/-- Assembly from the two finite completeness certificates. -/
theorem mixedImageSpace_eq_mixedSpace_of_certificates
    (heval : ∀ i j, selectedEvaluation (exteriorBasisForm j) i =
      coefficientEvaluationMatrix i j)
    (hkernel : ∀ c : Fin 1221 → ZMod 2, coefficientEvaluationMatrix *ᵥ c = 0 →
      c = radicalCoefficientMatrix *ᵥ freeCoefficients c) :
    mixedImageSpace = mixedSpace := by
  apply le_antisymm
  · rw [← radicalSpan_mixed_image]
    exact Submodule.map_mono (exteriorRadical_le_radicalSpan_of_certificates heval hkernel)
  · exact mixedSpace_le_mixedImageSpace

/-- Conditional assembly of the universal row factorization. -/
theorem radical_mixed_factorization_of_certificates
    (heval : ∀ i j, selectedEvaluation (exteriorBasisForm j) i =
      coefficientEvaluationMatrix i j)
    (hkernel : ∀ c : Fin 1221 → ZMod 2, coefficientEvaluationMatrix *ᵥ c = 0 →
      c = radicalCoefficientMatrix *ᵥ freeCoefficients c)
    (R : BinaryMatrix) (hR : R ∈ exteriorRadical displacementVectors) :
    mixedEmbeddingᵀ * R = mixedEvaluation R * restrictionExtraction * (matrixA - 1) :=
  radicalSpan_factorization R
    (exteriorRadical_le_radicalSpan_of_certificates heval hkernel hR)

/-- The checked forms span the entire actual exterior radical. -/
theorem RadicalCertificate.exteriorRadical_eq_radicalSpan :
    exteriorRadical displacementVectors = radicalSpan :=
  le_antisymm
    (exteriorRadical_le_radicalSpan_of_certificates selectedEvaluation_basis coefficient_kernel)
    radicalSpan_le

/-- The actual radical's mixed image is the displayed forty-generator space. -/
theorem mixedImageSpace_eq_mixedSpace : mixedImageSpace = mixedSpace := by
  change (exteriorRadical displacementVectors).map mixedEvaluation = mixedSpace
  rw [exteriorRadical_eq_radicalSpan]
  exact radicalSpan_mixed_image

/-- Every radical form's H rows factor through the displacement coordinates. -/
theorem radical_mixed_factorization (R : BinaryMatrix)
    (hR : R ∈ exteriorRadical displacementVectors) :
    mixedEmbeddingᵀ * R = mixedEvaluation R * restrictionExtraction * (matrixA - 1) := by
  rw [exteriorRadical_eq_radicalSpan] at hR
  exact radicalSpan_factorization R hR

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership
