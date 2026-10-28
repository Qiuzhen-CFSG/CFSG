module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.Projector
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.LeftKernel
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.KernelReduction
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.RightKernel
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.Completion

/-!
# The degree-1792 rank-one membership certificate

The checked left and right kernels make the published rank-one idempotent
orthogonal to the singular algebra element. The packed-expression equality
and the elimination certificate prove that their sum is a unit. The finite-ring
projector criterion then puts the idempotent in every algebra containing the
literal generator pair, without additional numerical premises.

The theorem below uses the original untransposed ATLAS matrices and the exact
published `vecMulVec nucleus (Pi.single 0 1)`. See `RankOne/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792
open Matrix RankOneCertificate

/-- Discharge the left-kernel obligation with the checked literal generator rows. -/
theorem rankOne_mem_of_right_kernel_and_unit
    (hkernel : singular.mulVec nucleus = 0)
    (hunit : IsUnit (singular + rankOne))
    (Q : Subalgebra (ZMod 2) (Matrix (Fin 1792) (Fin 1792) (ZMod 2)))
    (hA : Data1792.first ∈ Q) (hB : Data1792.second ∈ Q) : rankOne ∈ Q :=
  rankOne_mem_of_completion_unit hkernel singular_left_kernel hunit Q hA hB

/-- Assembly interface for independent verification of the saved packed matrix
and its invertible completion. The unconditional theorem below supplies all
three numerical certificates. -/
theorem rankOne_mem_of_packed_certificates
    (hkernel : singular.mulVec nucleus = 0)
    (hrows : packedSingular = singular)
    (hunit : IsUnit packedCompletion)
    (Q : Subalgebra (ZMod 2) (Matrix (Fin 1792) (Fin 1792) (ZMod 2)))
    (hA : Data1792.first ∈ Q) (hB : Data1792.second ∈ Q) : rankOne ∈ Q := by
  apply rankOne_mem_of_right_kernel_and_unit hkernel _ Q hA hB
  simpa only [packedCompletion, hrows] using hunit

/-- The exact published rank-one matrix belongs to every binary subalgebra
containing the literal, untransposed degree-1792 ATLAS pair. -/
theorem rankOne_mem
    (Q : Subalgebra (ZMod 2) (Matrix (Fin 1792) (Fin 1792) (ZMod 2)))
    (hA : Data1792.first ∈ Q) (hB : Data1792.second ∈ Q) : rankOne ∈ Q :=
  rankOne_mem_of_packed_certificates singular_right_kernel
    packedSingular_eq_singular packedCompletion_isUnit Q hA hB

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792
