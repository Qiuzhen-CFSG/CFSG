module
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.OddPrimeRankOneSylow

/-!
# Odd-prime ranks of complementary centralizers

Choose an order-s cyclic subgroup of K. Its intersection with a subgroup
centralizing K lies in Z(K); if Z(K) has exponent two and s is odd, that
intersection is trivial. The commuting product therefore contributes one
independent direction in addition to the complementary subgroup's rank.
If both factors centralize an involution whose centralizer has rank at
most two, the complementary subgroup has rank at most one. Its Sylow
s-subgroups are cyclic, so the bound passes to every surjective image.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.2.17,
printed p.39. We use a lower bound, which also covers nonprime SL₂ fields.
-/

public section
open Subgroup Theory.GroupTheory

namespace Subgroup

/-- A commuting subgroup gains an independent odd-prime direction from K
when the center of K has exponent dividing two. -/
theorem one_add_primeRank_le_sup_of_centralizes
    {G : Type*} [Group G] [Finite G] {s : ℕ} [Fact s.Prime]
    (hs : Odd s) (K J : Subgroup G) (hJ : J ≤ centralizer (K : Set G))
    (hcenter : ∀ x : center K, x ^ 2 = 1) (hdiv : s ∣ Nat.card K) :
    1 + primeRank s J ≤ primeRank s (K ⊔ J : Subgroup G) := by
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := K) s hdiv
  let U := zpowers (a : G)
  have hUK : U ≤ K := zpowers_le.mpr a.property
  have hUc : Nat.card U = s := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective K.subtype K.subtype_injective a).trans ha
  have hUp (u : U) : u ^ s = 1 := hUc ▸ (pow_card_eq_one' (x := u))
  have hUJ : U ≤ centralizer (J : Set G) :=
    hUK.trans (le_centralizer_iff.mp hJ)
  have hdis : Disjoint U J := by
    apply disjoint_iff_inf_le.mpr
    rintro x ⟨hxU, hxJ⟩
    have hxK : x ∈ K := hUK hxU
    have hxc : (⟨x, hxK⟩ : K) ∈ center K := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (hJ hxJ y y.property)
    have hx2 : x ^ 2 = 1 :=
      congrArg (fun y : center K => (y : G)) (hcenter ⟨⟨x, hxK⟩, hxc⟩)
    have hxs : x ^ s = 1 := congrArg Subtype.val (hUp ⟨x, hxU⟩)
    exact (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.coprime_two_left.mpr hs) (orderOf_dvd_of_pow_eq_one hx2)
      (orderOf_dvd_of_pow_eq_one hxs)))
  let : CommGroup U := IsMulCommutative.instCommGroup
  have hUr : 1 ≤ primeRank s U :=
    primeRank_ge_of_elementary_embedding hUp (by simpa using hUc)
      (MonoidHom.id U) Function.injective_id
  have hr := U.primeRank_sup_eq_add_of_disjoint_commuting J hdis hUJ s
  have hle := primeRank_le_of_injective s
    (inclusion (sup_le_sup_right hUK J)) (inclusion_injective _)
  omega

/-- A local involution-centralizer bound forces the complementary subgroup
and every surjective image of it to have odd prime rank at most one. -/
theorem complementary_primeRank_le_one
    {G H : Type*} [Group G] [Finite G] [Group H]
    {s : ℕ} [Fact s.Prime] (hs : Odd s)
    (K J : Subgroup G) (hJ : J ≤ centralizer (K : Set G))
    (hcenter : ∀ x : center K, x ^ 2 = 1) (hdiv : s ∣ Nat.card K)
    (z : G) (hzK : z ∈ K) (hKz : K ≤ centralizer ({z} : Set G))
    (hr : primeRank s (centralizer ({z} : Set G)) ≤ 2)
    (f : J →* H) (hf : Function.Surjective f) :
    primeRank s J ≤ 1 ∧ primeRank s H ≤ 1 := by
  have hJz : J ≤ centralizer ({z} : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (hJ hx z hzK).symm
  have hle := primeRank_le_of_injective s
    (inclusion (sup_le hKz hJz)) (inclusion_injective _)
  have hlower := one_add_primeRank_le_sup_of_centralizes hs K J hJ hcenter hdiv
  have hJrank : primeRank s J ≤ 1 := by omega
  let P : Sylow s J := Classical.choice inferInstance
  exact ⟨hJrank, P.primeRank_le_one_of_surjective
    (P.isCyclic_of_odd_of_primeRank_le_one hs hJrank) f hf⟩

end Subgroup
