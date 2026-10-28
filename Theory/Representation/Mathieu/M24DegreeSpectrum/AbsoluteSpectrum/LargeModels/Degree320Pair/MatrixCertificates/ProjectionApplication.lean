module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.FiniteProjection
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates.DensityCriterion

/-!
# A short rank-one membership certificate for the degree-320 generators

For the literal stored column and covector, their pairing being one makes the
outer product a projection. Two annihilation identities and one right inverse
of the complementary sum put this projection in the generated algebra. This
discharges exactly the per-variant obligation in `RankOneMembership`, without
requiring evaluation of the degree-319 polynomial from the discovery record.

The untrusted inverse candidates are reproduced by `source/discover_complements.py`.
They still require Lean checks; ATLAS attribution is in `../source/README.md`.
-/

public noncomputable section

namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates
open Matrix

theorem rankOne_mem_of_complement (variant : Bool) (T Ti : Mat)
    (hT : T ∈ generated variant)
    (hv : T.mulVec (column variant) = 0)
    (hl : Matrix.vecMul (covector variant) T = 0)
    (hp : covector variant ⬝ᵥ column variant = 1)
    (hi : (T + Matrix.vecMulVec (column variant) (covector variant)) * Ti = 1) :
    Matrix.vecMulVec (column variant) (covector variant) ∈ generated variant := by
  apply Subalgebra.mem_of_idempotent_complement (generated variant) T _ hT
  · rw [Matrix.mul_vecMulVec, hv]
    simp
  · rw [Matrix.vecMulVec_mul, hl]
    simp
  · rw [Matrix.vecMulVec_mul_vecMulVec, hp]
    simp
  · exact isUnit_iff_exists_inv.mpr ⟨Ti, hi⟩
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates
