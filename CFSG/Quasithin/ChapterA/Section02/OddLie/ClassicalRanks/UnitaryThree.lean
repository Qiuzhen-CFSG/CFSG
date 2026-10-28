module

public import Theory.SpecificGroups.SU3.OddDefiningRank

/-!
# The degree-one restriction for odd PSU₃ in A.2.17

The actual projective unitary group over a field of order `(p^e)^2`
contains an elementary abelian defining-prime subgroup of order `p^(2e)`.
Consequently the ordinary defining-prime rank bound by two forces `e=1`.
In particular, fixed-field degree two has ordinary rank at least four.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.2.17, printed p.39 (PDF p.50), the strongly quasithin three-dimensional
unitary branch. These deductions supply the defining-rank input; the full
family elimination and its other source premises belong to the assembly.
-/

public section

namespace CFSG.Quasithin.ChapterA.Section02

open BenderSuzuki.MatrixGroups

variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
  {p e : ℕ} [Fact p.Prime]

/-- The ordinary defining-prime rank bound in the strongly quasithin branch
forces the fixed field to have prime order. -/
theorem psu3_fieldExponent_eq_one (hp : p ≠ 2)
    (hc : Nat.card F = (p ^ e) ^ 2) (he : 1 ≤ e)
    (hconj : ∀ x : F, J.conj x = x ^ (p ^ e))
    (hr : primeRank p (ProjectiveSpecialUnitaryMatrixGroup J) ≤ 2) : e = 1 := by
  have := HermitianForm.OddDefiningRank.two_mul_fieldExponent_le_primeRank
    J hp (by omega) hc hconj
  omega

/-- At fixed-field degree two, the ordinary defining-prime rank is at least four. -/
theorem psu3_square_four_le_primeRank (hp : p ≠ 2)
    (hc : Nat.card F = (p ^ 2) ^ 2)
    (hconj : ∀ x : F, J.conj x = x ^ (p ^ 2)) :
    4 ≤ primeRank p (ProjectiveSpecialUnitaryMatrixGroup J) := by
  simpa using HermitianForm.OddDefiningRank.two_mul_fieldExponent_le_primeRank
    J hp (by decide : 0 < 2) hc hconj

end CFSG.Quasithin.ChapterA.Section02
