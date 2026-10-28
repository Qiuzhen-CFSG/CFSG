module
public import Theory.GroupTheory.QuasithinBasic

/-!
# Vanishing prime rank and surjective images

A finite group has `p`-rank zero exactly when `p` does not divide its order.
Cauchy's theorem supplies a nontrivial cyclic `p`-subgroup in one direction;
in the other direction every `p`-subgroup is trivial. Divisibility of orders
then transports vanishing prime rank along surjections.

This is the rank-zero step of Aschbacher–Smith, *The Classification of
Quasithin Groups*, combined manuscript (1 March 2004), Lemma A.2.7, p. 34.
-/

public section
namespace PrimeRank

/-- Vanishing prime rank is equivalent to prime-to-`p` group order. -/
theorem eq_zero_iff_not_dvd_card {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] : primeRank p G = 0 ↔ ¬ p ∣ Nat.card G := by
  constructor
  · intro h hdvd
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) p hdvd
    let A := Subgroup.zpowers g
    have hcard : Nat.card A = p := (Nat.card_zpowers g).trans hg
    have hAp : IsPGroup p A := IsPGroup.of_card (n := 1) (by simpa using hcard)
    have hrank : Group.rank A ≤ primeRank p G :=
      le_csSup (Theory.GroupTheory.primeRank_bdd p) ⟨A, hAp, inferInstance, inferInstance, le_rfl⟩
    have hrank0 : Group.rank A = 0 := Nat.eq_zero_of_le_zero (h ▸ hrank)
    let := Group.rank_eq_zero_iff.mp hrank0
    have hcard1 : Nat.card A = 1 := Nat.card_unique
    exact (Fact.out : p.Prime).ne_one (hcard.symm.trans hcard1)
  · intro h
    apply Nat.eq_zero_of_le_zero
    apply csSup_le'
    rintro n ⟨A, hAp, _, _, hn⟩
    have hA : Subsingleton A := by
      by_contra hA
      let : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
      obtain ⟨k, hk, hcard⟩ := hAp.nontrivial_iff_card.mp inferInstance
      have hdvd : p ∣ Nat.card A := hcard ▸ dvd_pow_self p (Nat.ne_of_gt hk)
      exact h (hdvd.trans (Subgroup.card_dvd_of_injective A.subtype A.subtype_injective))
    let := hA
    simpa only [Group.rank_eq_zero A] using hn

/-- Vanishing prime rank passes to every surjective image. -/
theorem eq_zero_of_surjective {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (h : primeRank p G = 0) : primeRank p H = 0 := by
  let : Finite H := Finite.of_surjective f hf
  apply eq_zero_iff_not_dvd_card.mpr
  intro hdvd
  exact eq_zero_iff_not_dvd_card.mp h
    (hdvd.trans (Subgroup.card_dvd_of_surjective f hf))

/-- A quotient of a group of prime rank zero again has prime rank zero. -/
theorem quotient_eq_zero {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (K : Subgroup G) [K.Normal]
    (h : primeRank p G = 0) : primeRank p (G ⧸ K) = 0 :=
  eq_zero_of_surjective (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K) h

end PrimeRank
