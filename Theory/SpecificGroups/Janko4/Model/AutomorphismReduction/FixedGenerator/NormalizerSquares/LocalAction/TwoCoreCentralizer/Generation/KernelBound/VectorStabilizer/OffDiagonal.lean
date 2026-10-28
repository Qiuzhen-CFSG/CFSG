module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.OffDiagonal.Transport
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.OffDiagonal.MixedTests

/-!
# Assembly of the off-diagonal vanishing argument

The transport lemmas derive the two actual mixed-generator constraints from
the supplied radical upper bound. The checked finite linear-system certificate
then kills D. Preservation of the nondegenerate invariant pairing kills B.

The final theorem discharges the finite-test premise of the retained
conditional assembly. The radical upper bound and identity restriction remain
explicit inputs, supplied independently by the full vector-stabilizer assembly.
See source/README.md for the 600-to-78-to-zero witness computation and the
original matrix conventions.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership

/-- Assembly once the two concrete mixed tests have been proved separating. -/
theorem offDiagonal_eq_zero_of_mixed_tests
    (htests : ∀ D : MixedMatrix,
      Dᵀ * mixedGenerator 0 + (mixedGenerator 0)ᵀ * D ∈ radicalKUpperSpace →
      Dᵀ * mixedGenerator 1 + (mixedGenerator 1)ᵀ * D ∈ radicalKUpperSpace → D = 0)
    (hrad : RadicalKUpperBound) (g : BinaryMatrixˣ)
    (hker : KernelConditions g) (hform : formPullback g invariantForm = invariantForm)
    (hext : g ∈ formStabilizer exteriorFormSpace) (hS : restrictionMatrix g = 1) :
    middleRightBlock g = 0 ∧ upperMiddleBlock g = 0 := by
  have hD := htests (middleRightBlock g)
    (OffDiagonal.mixed_constraint hrad g hker hext hS 0)
    (OffDiagonal.mixed_constraint hrad g hker hext hS 1)
  exact ⟨hD, OffDiagonal.upperMiddle_zero_of_middleRight_zero g hker hform hS hD⟩

/-- The two off-diagonal kernel blocks vanish under the radical upper bound
and identity restriction, using the certified actual mixed-generator tests. -/
theorem offDiagonal_eq_zero
    (hrad : RadicalKUpperBound) (g : BinaryMatrixˣ)
    (hker : KernelConditions g) (hform : formPullback g invariantForm = invariantForm)
    (hext : g ∈ formStabilizer exteriorFormSpace) (hS : restrictionMatrix g = 1) :
    middleRightBlock g = 0 ∧ upperMiddleBlock g = 0 :=
  offDiagonal_eq_zero_of_mixed_tests OffDiagonal.mixed_tests_eq_zero hrad g hker hform hext hS

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer
