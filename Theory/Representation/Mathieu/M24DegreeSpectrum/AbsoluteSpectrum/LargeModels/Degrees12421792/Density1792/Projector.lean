module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.Criteria
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.CertificateData

/-!
# A rank-one certificate from an invertible completion

For the literal candidate S and proposed kernel vector u, the matrix P=u e₀ᵀ
is idempotent since u₀=1. The two kernel identities make S and P orthogonal.
If S+P is a unit, the finite-ring criterion puts P in every algebra containing
the ATLAS pair. The kernel identities and the unit certificate remain explicit
numerical obligations; no density or irreducibility is assumed.

See `source/README.md` for the exact word expression, ATLAS provenance, and
independent column-orbit certificate used by the density assembly.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792
open Matrix
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792

theorem rankOne_mem_of_completion_unit
    (hkernel : singular.mulVec nucleus = 0)
    (hrow : vecMul (Pi.single 0 1) singular = 0)
    (hunit : IsUnit (singular + rankOne))
    (Q : Subalgebra (ZMod 2) (Matrix (Fin 1792) (Fin 1792) (ZMod 2)))
    (hA : Data1792.first ∈ Q) (hB : Data1792.second ∈ Q) : rankOne ∈ Q := by
  apply projector_mem Q singular rankOne (singular_mem Q hA hB) _ _ _ hunit
  · rw [rankOne, mul_vecMulVec, hkernel, zero_vecMulVec]
  · rw [rankOne, vecMulVec_mul, hrow, vecMulVec_zero]
  · rw [rankOne, vecMulVec_mul_vecMulVec, single_one_dotProduct, nucleus_zero, one_smul]
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792
