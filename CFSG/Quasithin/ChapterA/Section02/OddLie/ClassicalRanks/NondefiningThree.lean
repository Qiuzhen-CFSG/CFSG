module

public import Theory.SpecificGroups.ProjectiveDimensionThree.NondefiningThreeRank
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# The dimension-three nondefining prime in A.2.17

Remark A.2.14 excludes a central cover of order three once the central
quotient has three-rank at most two. For the linear and unitary groups of
dimension three, the earlier source deduction Oᵣ(G)=1 makes this a
nondefining prime. The matrix results apply to the actual PSL quotient
and the actual projective special unitary image, and transport across a
specified multiplicative isomorphism.

Both matrix-lift branches are proved in the imported Theory modules,
including the extraspecial possibility. The unconditional results below
therefore supply the source's nondefining three-rank input without any
remaining matrix premise. The earlier conditional interfaces are retained.
The multiplier and Oᵣ(G)=1 deductions belong to the source assembly;
no bound on defining-prime ranks is asserted here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.2.17 and Remark A.2.14, printed pp.37–39.
-/

public section

namespace CFSG.Quasithin.ChapterA.Section02.ClassicalRanks.NondefiningThree
open Matrix Matrix.ProjectiveDimensionThree BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative

variable {F : Type*} [Field F] [Finite F] {r e : ℕ} [Fact r.Prime]

private instance finite_pgl : Finite PGL(3,F) :=
  Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective

omit [Finite F] in
private theorem three_ne_zero [CharP F r] (hr : r ≠ 3) : (3 : F) ≠ 0 := by
  change (↑(3 : ℕ) : F) ≠ 0
  rw [ne_eq, CharP.cast_eq_zero_iff F r]
  intro hd
  exact hr ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) Nat.prime_three).mp hd)

section Conditional

variable (hnoncommuting : ∀ H : Subgroup (GL (Fin 3) F),
  IsMulCommutative (H.map ProjGenLinGroup.mk) → ¬ IsMulCommutative H →
    Nat.card (H.map ProjGenLinGroup.mk) ≤ 3 ^ 2)

include hnoncommuting

/-- The PSL₃ input with the source field parameters, conditional on the
remaining noncommuting matrix calculation. -/
theorem psl3_threeRank_le_two_of_noncommuting_bound
    (hF : Nat.card F = r ^ e) (_he : 1 ≤ e) (_hr2 : r ≠ 2) (hr3 : r ≠ 3) :
    primeRank 3 PSL(3,F) ≤ 2 := by
  let := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow
    (by simpa only [← Nat.card_eq_fintype_card] using hF)
  exact psl_primeRank_three_le_two_of_noncommuting_bound (three_ne_zero hr3) hnoncommuting

/-- The corresponding input for an arbitrary actual Hermitian form and the
source quadratic-field conjugation. -/
theorem psu3_threeRank_le_two_of_noncommuting_bound
    (J : HermitianForm 3 F) (hF : Nat.card F = (r ^ e) ^ 2)
    (_hc : ∀ x, J.conj x = x ^ (r ^ e)) (_he : 1 ≤ e)
    (_hr2 : r ≠ 2) (hr3 : r ≠ 3) :
    primeRank 3 (ProjectiveSpecialUnitaryMatrixGroup J) ≤ 2 := by
  let := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow (f := e * 2)
    (by simpa only [← Nat.card_eq_fintype_card, pow_mul] using hF)
  exact psu_primeRank_three_le_two_of_noncommuting_bound (three_ne_zero hr3) hnoncommuting J

/-- Transport of the actual PSL₃ matrix result to a multiplicatively isomorphic group. -/
theorem threeRank_le_two_of_psl3_equiv_of_noncommuting_bound
    {G : Type*} [Group G] (iso : G ≃* PSL(3,F))
    (hF : Nat.card F = r ^ e) (he : 1 ≤ e) (hr2 : r ≠ 2) (hr3 : r ≠ 3) :
    primeRank 3 G ≤ 2 := by
  let : Finite G := Finite.of_equiv PSL(3,F) iso.symm.toEquiv
  rw [Theory.GroupTheory.primeRank_equiv 3 iso]
  exact psl3_threeRank_le_two_of_noncommuting_bound hnoncommuting hF he hr2 hr3

/-- Transport of the literal projective unitary image result to an isomorphic group. -/
theorem threeRank_le_two_of_psu3_equiv_of_noncommuting_bound
    {G : Type*} [Group G] (J : HermitianForm 3 F)
    (iso : G ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hF : Nat.card F = (r ^ e) ^ 2) (hc : ∀ x, J.conj x = x ^ (r ^ e))
    (he : 1 ≤ e) (hr2 : r ≠ 2) (hr3 : r ≠ 3) : primeRank 3 G ≤ 2 := by
  let : Finite G := Finite.of_equiv (ProjectiveSpecialUnitaryMatrixGroup J) iso.symm.toEquiv
  rw [Theory.GroupTheory.primeRank_equiv 3 iso]
  exact psu3_threeRank_le_two_of_noncommuting_bound hnoncommuting J hF hc he hr2 hr3

end Conditional

/-- The nondefining three-rank bound for the actual PSL₃ with the source field
parameters. This discharges the rank input in the center-of-order-three case. -/
theorem psl3_threeRank_le_two
    (hF : Nat.card F = r ^ e) (_he : 1 ≤ e) (_hr2 : r ≠ 2) (hr3 : r ≠ 3) :
    primeRank 3 PSL(3,F) ≤ 2 := by
  let := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow
    (by simpa only [← Nat.card_eq_fintype_card] using hF)
  exact psl_primeRank_three_le_two (three_ne_zero hr3)

/-- The nondefining three-rank bound for the actual projective special unitary
group of any Hermitian form with the source quadratic-field conjugation. -/
theorem psu3_threeRank_le_two
    (J : HermitianForm 3 F) (hF : Nat.card F = (r ^ e) ^ 2)
    (_hc : ∀ x, J.conj x = x ^ (r ^ e)) (_he : 1 ≤ e)
    (_hr2 : r ≠ 2) (hr3 : r ≠ 3) :
    primeRank 3 (ProjectiveSpecialUnitaryMatrixGroup J) ≤ 2 := by
  let := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow (f := e * 2)
    (by simpa only [← Nat.card_eq_fintype_card, pow_mul] using hF)
  exact psu_primeRank_three_le_two (three_ne_zero hr3) J

/-- The source rank bound transported from the actual PSL₃ quotient through
a specified multiplicative isomorphism, with no remaining matrix premise. -/
theorem threeRank_le_two_of_psl3_equiv
    {G : Type*} [Group G] (iso : G ≃* PSL(3,F))
    (hF : Nat.card F = r ^ e) (he : 1 ≤ e) (hr2 : r ≠ 2) (hr3 : r ≠ 3) :
    primeRank 3 G ≤ 2 := by
  let : Finite G := Finite.of_equiv PSL(3,F) iso.symm.toEquiv
  rw [Theory.GroupTheory.primeRank_equiv 3 iso]
  exact psl3_threeRank_le_two hF he hr2 hr3

/-- The source rank bound transported from the literal projective unitary
image through a specified multiplicative isomorphism. -/
theorem threeRank_le_two_of_psu3_equiv
    {G : Type*} [Group G] (J : HermitianForm 3 F)
    (iso : G ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hF : Nat.card F = (r ^ e) ^ 2) (hc : ∀ x, J.conj x = x ^ (r ^ e))
    (he : 1 ≤ e) (hr2 : r ≠ 2) (hr3 : r ≠ 3) : primeRank 3 G ≤ 2 := by
  let : Finite G := Finite.of_equiv (ProjectiveSpecialUnitaryMatrixGroup J) iso.symm.toEquiv
  rw [Theory.GroupTheory.primeRank_equiv 3 iso]
  exact psu3_threeRank_le_two J hF hc he hr2 hr3

end CFSG.Quasithin.ChapterA.Section02.ClassicalRanks.NondefiningThree
