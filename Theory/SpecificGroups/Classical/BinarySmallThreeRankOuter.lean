module

public import Theory.SpecificGroups.Classical.RankOneOuter
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank
public import Theory.SpecificGroups.SU3.EvenSemilinear.CyclicOuter

/-!
# Outer groups of binary signed-three groups of small three-rank

The concrete cubic rank witnesses rule out even degree in PSL₃ and odd
fixed-field degree in PSU₃. In the remaining degrees the diagonal outer
image vanishes, leaving the abelian field–graph image, respectively the
cyclic unitary field image. Simplicity in the unitary calculation is
inherited from the supplied group.

Source: Aschbacher–Smith, proof of 13.6.6(ii), printed p.927;
GLS3, Theorem 2.5.12 and §2.7, `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
open Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.SpecificGroups.Classical.BinarySmallThreeRankOuter
variable {F : Type*} [Field F] [Finite F] {n : ℕ}

/-- Small three-rank forces the opposite-sign linear parameter. -/
theorem linear_degree_odd (hcard : Nat.card F = 2 ^ n)
    (hr : primeRank 3 PSL(3,F) ≤ 1) : Odd n := by
  apply Nat.not_even_iff_odd.mp
  intro he
  have h := SignedThreeCubicRank.linear_projective hcard he
  omega

/-- The rank restriction discharges the congruence in the linear outer calculation. -/
theorem linear_outer_isMulCommutative (hn : 0 < n) (hcard : Nat.card F = 2 ^ n)
    (hr : primeRank 3 PSL(3,F) ≤ 1) : IsMulCommutative (MulAut.Outer PSL(3,F)) := by
  have ho := linear_degree_odd hcard hr
  apply Matrix.PSL3.OuterSolvable.outer_isMulCommutative_of_two_power_card_mod_three
    F hn hcard
  rw [Nat.BinaryTorusParity.two_pow_mod_three, if_neg]
  exact Nat.not_even_iff_odd.mpr ho ∘ Nat.even_iff.mpr

open BenderSuzuki.MatrixGroups

/-- Small three-rank forces even fixed-field degree for the actual Hermitian model. -/
theorem unitary_degree_even (J : HermitianForm 3 F) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hr : primeRank 3 (ProjectiveSpecialUnitaryMatrixGroup J) ≤ 1) : Even n := by
  apply Nat.not_odd_iff_even.mp
  intro ho
  have h := SignedThreeCubicRank.unitary_projective J hn hcard hconj ho
  omega

/-- The rank restriction discharges all parameter premises of unitary outer cyclicity. -/
theorem unitary_outer_isCyclic (J : HermitianForm 3 F)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hn : 1 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hr : primeRank 3 (ProjectiveSpecialUnitaryMatrixGroup J) ≤ 1) :
    IsCyclic (MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J)) :=
  HermitianForm.EvenSemilinear.outer_isCyclic_of_even J hn
    (unitary_degree_even J (by omega) hcard hconj hr) hcard hconj

end Theory.SpecificGroups.Classical.BinarySmallThreeRankOuter
