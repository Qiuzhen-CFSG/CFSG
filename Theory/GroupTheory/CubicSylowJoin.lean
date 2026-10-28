module

public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.PResidual.PrimeSet
public import Mathlib.GroupTheory.Sylow
/-!
# Index-three joins of normalized {2,3}-subgroups

A Sylow two-subgroup normalizing a {2,3}-subgroup with Sylow three-subgroups
of order three has index three in their join. The normal-product index formula
makes the index divide the normalized subgroup order. It is odd by the Sylow
condition, and its three-part is at most three. Index one would make the
normalized subgroup a two-group. A second form needs only an order dividing
three times a power of two and the exclusion of a two-group.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.22–23, printed pp.932–933. These are general finite-group lemmas.
-/

public section
open Subgroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The normalized {2,3}-subgroup and its actual order-three Sylow force index three. -/
theorem normalized_twoThree_join_index (U : Sylow 2 G) (A : Subgroup G)
    (hn : (U : Subgroup G) ≤ normalizer (A : Set G))
    (hpi : IsPiGroup twoThreePrimes A)
    (V : Sylow 3 A) (hV : Nat.card V = 3) :
    (U : Subgroup G).relIndex (A ⊔ U) = 3 := by
  let d := (U : Subgroup G).relIndex (A ⊔ U)
  have hd : d ∣ Nat.card A := by
    dsimp only [d]
    rw [relIndex_sup_of_normalizes A U hn]
    exact relIndex_dvd_card _ _
  have hodd : ¬ 2 ∣ d :=
    (U.subtype (show (U : Subgroup G) ≤ A ⊔ U from le_sup_right)).not_dvd_index
  have hp : d = 3 ^ d.primeFactorsList.length := by
    apply Nat.eq_prime_pow_of_unique_prime_dvd (index_ne_zero_of_finite)
    intro p hprime hpd
    have hh := (IsPiGroup_iff twoThreePrimes A).mp hpi ⟨p, hprime⟩ (hpd.trans hd)
    change p = 2 ∨ p = 3 at hh
    exact hh.resolve_left (fun h => hodd (h ▸ hpd))
  have hpow : 3 ^ d.primeFactorsList.length ∣ Nat.card V :=
    V.pow_dvd_card_of_pow_dvd_card (hp ▸ hd)
  rw [hV] at hpow
  have hlen : d.primeFactorsList.length ≤ 1 := by
    have hle := Nat.le_of_dvd (by decide : 0 < 3) hpow
    have : 3 ^ d.primeFactorsList.length ≤ 3 ^ 1 := by simpa using hle
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 3)).mp this
  have hne : d ≠ 1 := by
    intro he
    have hAU : A ≤ U := le_sup_left.trans (relIndex_eq_one.mp he)
    have hA := U.isPGroup'.to_le hAU
    have hthree : 3 ∣ Nat.card A := hV ▸ card_subgroup_dvd_card (V : Subgroup A)
    obtain ⟨k, hk⟩ := hA.exists_card_eq
    rw [hk] at hthree
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hthree)
  have hlen1 : d.primeFactorsList.length = 1 := by
    by_contra h
    have : d.primeFactorsList.length = 0 := by omega
    simp [this] at hp
    exact hne hp
  simpa [hlen1] using hp

/-- A non-two-group whose order divides three times a power of two has
index three over any normalizing Sylow two-subgroup. -/
theorem normalized_cubic_join_index_of_card_dvd (U : Sylow 2 G) (A : Subgroup G)
    (hn : (U : Subgroup G) ≤ normalizer (A : Set G))
    (hc : ∃ n, Nat.card A ∣ 3 * 2 ^ n) (hA : ¬ IsPGroup 2 A) :
    (U : Subgroup G).relIndex (A ⊔ U) = 3 := by
  obtain ⟨n, hncard⟩ := hc
  have hd : (U : Subgroup G).relIndex (A ⊔ U) ∣ 3 * 2 ^ n := by
    rw [relIndex_sup_of_normalizes A U hn]
    exact (relIndex_dvd_card _ _).trans hncard
  have hodd : ¬ 2 ∣ (U : Subgroup G).relIndex (A ⊔ U) :=
    (U.subtype (show (U : Subgroup G) ≤ A ⊔ U from le_sup_right)).not_dvd_index
  have hcop : ((U : Subgroup G).relIndex (A ⊔ U)).Coprime 2 :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr hodd).symm
  have hd3 := (hcop.pow_right n).dvd_of_dvd_mul_right hd
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd3 with he | he
  · exact (hA (U.isPGroup'.to_le (le_sup_left.trans (relIndex_eq_one.mp he)))).elim
  · exact he
end Subgroup
