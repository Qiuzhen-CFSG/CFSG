module

public import Theory.SpecificGroups.SU3.EvenTwoRank.Automorphisms
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Coverage

/-!
# Binary PSU₃ automorphism rank for arbitrary Hermitian forms

For a matrix field of order `(2^n)^2`, with the stored involution equal to
the `2^n`-power Frobenius and `n ≥ 2`, the actual projective special unitary
group has automorphism two-rank at most `n+1`.

The fixed field has order `2^n`. The proved semilinear coverage theorem
therefore discharges the structural premise of the rank calculation for
the standard form. A genuine Hermitian change of basis transports the full
automorphism group back to the given form. Together with `two_rank`, this
gives the two numerical inputs for the linear/unitary graph-field pair.

Source: Aschbacher–Smith, the automorphism-rank table on printed p.356 and
16.1.7(3b), p.1172. The uniform bound by `n` printed in the argument on
p.1180 is not used.
-/

public section

open Theory.GroupTheory
namespace BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank

variable {E : Type*} [Field E] [Finite E]

/-- The binary PSU₃ automorphism bound, with no coverage or numerical premise
and no restriction on the Gram matrix of the Hermitian form. -/
theorem automorphism_two_rank_le (J : HermitianForm 3 E)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ (2 ^ n)) :
    primeRank 2 (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ n + 1 := by
  have hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  apply automorphism_two_rank_le_of_standard_coverage J (by omega) hcard hconj
  exact (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J).semilinear_coverage
    n hn rfl hcard hfixed

end BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank
