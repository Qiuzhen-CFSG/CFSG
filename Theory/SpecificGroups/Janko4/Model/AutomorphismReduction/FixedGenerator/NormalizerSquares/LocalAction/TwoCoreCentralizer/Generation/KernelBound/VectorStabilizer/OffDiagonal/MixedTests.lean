module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.OffDiagonal.MixedTests.Checked

/-!
# The two mixed-generator tests force the off-diagonal block to vanish

For the actual 12-by-50 binary matrix D, membership of both mixed tests in
the actual thirteen-generator radical-K upper space forces every entry
of D to vanish. The certificate uses full Gaussian remainders and a checked
left inverse on all 600 entries. No auxiliary hypothesis is imposed.

Source: ../source/README.md; the reproducible witness selection and its
trust boundary are documented in MixedTests/source/README.md.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.OffDiagonal
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership

/-- The two literal mixed-generator tests have trivial common kernel
modulo the span of the thirteen literal radical-K upper matrices. -/
theorem mixed_tests_eq_zero (D : MixedMatrix)
    (h0 : Dᵀ * mixedGenerator 0 + (mixedGenerator 0)ᵀ * D ∈ radicalKUpperSpace)
    (h1 : Dᵀ * mixedGenerator 1 + (mixedGenerator 1)ᵀ * D ∈ radicalKUpperSpace) :
    D = 0 := by
  apply MixedTestCertificate.eq_zero_of_checks MixedTestCertificate.pivotChecks
    MixedTestCertificate.allRowChecks D
  intro t
  fin_cases t
  · exact h0
  · exact h1

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.OffDiagonal
