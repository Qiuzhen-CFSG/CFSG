module

public import Theory.GroupTheory.TwoLocalRankOfCentralizers
public import Theory.SpecificGroups.Classical.DefiningLocalRank.FourCentralizer
public import Theory.SpecificGroups.Classical.DefiningLocalRank.LinearCentralizer
public import Theory.SpecificGroups.Classical.DefiningLocalRank.UnitaryCentralizer
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# The defining-prime two-local rank of the signed degree-three groups

For q=p^e with p odd, each involution centralizer has p-rank at most e,
and each four-group centralizer has p-rank zero. The characteristic central
Omega subgroup of every nontrivial two-subgroup has order two or four.
Applying the actual normalizer action therefore gives m₂,p≤max(2,e) in
both PSL₃(q) and PSU₃(q). The unitary statement uses the original stored
Hermitian form and Frobenius involution, with no standard-form premise.

Source: Aschbacher–Smith A.2.12, printed p.36. Ordinary defining-prime rank
can be 2e, so its bound cannot replace this local calculation.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace Theory.SpecificGroups.DefiningLocalRank

/-- The source defining-prime local bound for the actual PSL₃ carrier. -/
theorem psl3_twoLocalPrimeRank_le_max
    {F : Type*} [Field F] [Finite F] {p e : ℕ} [Fact p.Prime]
    (hp : Odd p) (he : 0 < e) (hcard : Nat.card F = p ^ e) :
    twoLocalPrimeRank p PSL(3,F) ≤ max 2 e := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (p := p) (f := e)
    (by simpa only [← Nat.card_eq_fintype_card] using hcard)
  have h2 := OddThreeRank.two_ne_zero_of_odd_card hp hcard
  apply Theory.GroupTheory.twoLocalPrimeRank_le_max_of_centralizers hp (psl3_two_rank_le h2)
    (psl3_involution_centralizer_rank hp he hcard)
  intro A hA hA4
  rw [psl3_four_centralizer_rank_zero h2 A hA hA4]
  decide

/-- The same source bound for every actual ternary Hermitian projective model. -/
theorem psu3_twoLocalPrimeRank_le_max
    {F : Type*} [Field F] [Finite F]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    {p e : ℕ} [Fact p.Prime] (hp : Odd p) (he : 0 < e)
    (hcard : Nat.card F = (p ^ e) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (p ^ e)) :
    twoLocalPrimeRank p (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) ≤
      max 2 e := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (p := p) (f := e * 2)
    (by simpa only [← Nat.card_eq_fintype_card,pow_mul] using hcard)
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have h2 := OddThreeRank.two_ne_zero_of_odd_card hp
    (show Nat.card F = p ^ (e * 2) from hcard.trans (pow_mul p e 2).symm)
  apply Theory.GroupTheory.twoLocalPrimeRank_le_max_of_centralizers hp (psu3_two_rank_le J h2)
    (Classical.DefiningLocalRank.UnitaryCentralizer.projective_involution_centralizer_rank
      J hp he hcard hconj)
  intro A hA hA4
  rw [psu3_four_centralizer_rank_zero J h2 A hA hA4]
  decide

end Theory.SpecificGroups.DefiningLocalRank
