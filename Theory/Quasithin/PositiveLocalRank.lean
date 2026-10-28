module
public import Theory.Quasithin.LocalRank
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# Positive local prime rank from a local order divisor

Cauchy's theorem turns a prime divisor of a finite subgroup order into a
rank-one elementary witness. When the subgroup is a two-local, the same
witness contributes to the two-local prime rank. In particular this applies
to the centralizer of a specified involution.

Source: Aschbacher--Smith, §A.2, printed pp.33--34, for the local rank
invariant. The concrete sporadic applications use their certified local orders.
-/

public section
namespace Theory.Quasithin
open Subgroup Theory.GroupTheory

/-- Cauchy's theorem gives a rank-one witness at every prime divisor. -/
theorem one_le_primeRank_of_dvd_card {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : p ∣ Nat.card G) : 1 ≤ primeRank p G := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hp
  let : IsElementaryAbelian p (zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hx ▸ pow_orderOf_eq_one x)
  exact IsElementaryAbelian.primeRank_ge_of_card (zpowers x)
    (by simpa only [Nat.card_zpowers, pow_one] using hx)

/-- A prime divisor of an actual two-local gives positive two-local rank. -/
theorem one_le_twoLocalPrimeRank_of_dvd_card {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (M : Subgroup G) (hM : IsTwoLocal M)
    (hp : p ∣ Nat.card M) : 1 ≤ twoLocalPrimeRank p G :=
  (one_le_primeRank_of_dvd_card hp).trans (hM.primeRank_le p)

/-- The centralizer of a specified involution is a literal two-local witness. -/
theorem one_le_twoLocalPrimeRank_of_dvd_involution_centralizer
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (t : G) (ht : orderOf t = 2)
    (hp : p ∣ Nat.card (centralizer ({t} : Set G))) : 1 ≤ twoLocalPrimeRank p G :=
  one_le_twoLocalPrimeRank_of_dvd_card _ (isTwoLocal_involution_centralizer ht) hp

end Theory.Quasithin
