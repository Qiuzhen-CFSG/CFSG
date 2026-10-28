module
public import Theory.SpecificGroups.Classical.ThreeCoverLocalRanks
public import Theory.SpecificGroups.Classical.ThreeCoverLocalRanks.OddLocal
public import Theory.Quasithin.LocalRank
/-!
# Ordinary and local cubic ranks for odd signed degree-three covers

The determinant-one ordinary bound is at most two. The literal normalizer
witnesses in `OddLocal` attain two, so both ordinary and two-local three-rank
are exactly two. The unitary statement retains the coefficient field of order
p² and the p-power field involution.

Source: Aschbacher--Smith, A.2.12(I.i), printed pp.36--37.
-/

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace Theory.SpecificGroups.Classical.ThreeCoverLocalRanks

private theorem ordinary_and_local_eq_two
    {G : Type*} [Group G] [Finite G]
    (hu : primeRank 3 G ≤ 2)
    (hw : ∃ R : Subgroup G, R ≠ ⊥ ∧ IsPGroup 2 R ∧
      2 ≤ primeRank 3 (normalizer (R : Set G))) :
    primeRank 3 G = 2 ∧ twoLocalPrimeRank 3 G = 2 := by
  obtain ⟨R, hR, hRp, hr⟩ := hw
  have hl := hr.trans ((show IsTwoLocal (normalizer (R : Set G)) from ⟨R,hR,hRp,rfl⟩).primeRank_le 3)
  have hle := twoLocalPrimeRank_le_primeRank (G := G) 3
  exact ⟨by omega, by omega⟩

/-- Both ranks of the odd-prime SL₃ cover are two at cubic-center parameters. -/
public theorem odd_prime_linear_rank_pair
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hcard : Nat.card F = p) (hmod : p % 3 = 1) :
    primeRank 3 SL(3,F) = 2 ∧ twoLocalPrimeRank 3 SL(3,F) = 2 := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime
    (by simpa only [← Nat.card_eq_fintype_card] using hcard)
  have h3 : (3 : F) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_three (by
    intro he
    norm_num [he] at hmod)
  exact ordinary_and_local_eq_two (special_odd_prime_rank_le_two h3)
    (linear_odd_prime_local_cubic_witness hp hcard hmod)

/-- Both ranks of the odd-prime SU₃ cover are two; q=p and the matrix
coefficient field has order p² with the displayed p-power involution. -/
public theorem odd_prime_unitary_rank_pair
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hcard : Nat.card F = p ^ 2)
    (hconj : ∀ x, J.conj x = x ^ p) (hmod : p % 3 = 2) :
    primeRank 3 J.specialSubgroup = 2 ∧ twoLocalPrimeRank 3 J.specialSubgroup = 2 := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow
    (by simpa only [← Nat.card_eq_fintype_card] using hcard)
  have h3 : (3 : F) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_three (by
    intro he
    norm_num [he] at hmod)
  exact ordinary_and_local_eq_two (unitary_odd_prime_rank_le_two J h3)
    (unitary_odd_prime_local_cubic_witness J hp hcard hconj hmod)
end Theory.SpecificGroups.Classical.ThreeCoverLocalRanks
