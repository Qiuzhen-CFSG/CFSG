module
public import Theory.GroupAction.ComponentRankAction.PrimeClosure
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Outside odd-prime actors and C-component rank

A normal subgroup of full p-rank two with p-prime center has p-prime
centralizer. If its outer automorphism group is a two-group, every
order-p actor acts internally and is absorbed by the subgroup.

For a C-component, quotient the ambient group by its actual two-core.
The component image is its intrinsic two-core quotient, with odd rank
unchanged. Coprime-kernel absorption lifts membership back to the original
component. Thus an outside prime actor forces component p-rank at most one.

Source: Aschbacher–Smith, A.3.18, printed pp.51–53, the centerless
outer-two branch; used in original 4.3.12(2), p.617.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.CComponentPrimeRank
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- An outside prime actor forces a rank drop when the center is prime to p
and every outer automorphism has two-power order. -/
theorem prime_actor_mem_of_full_rank (B : Subgroup G) [B.Normal]
    (hz : Nat.Coprime p (Nat.card (center B)))
    (hr : 2 ≤ primeRank p B) (hG : primeRank p G ≤ 2)
    (ho : Odd p) (hout : IsPGroup 2 (MulAut.Outer B))
    (x : G) (hx : orderOf x = p) : x ∈ B := by
  let f : G →* MulAut B := MulAut.conjNormal
  have hk : Nat.Coprime p (Nat.card f.ker) := by
    rw [show f.ker = centralizer (B : Set G) from MulAut.conjNormal_ker_eq_centralizer B]
    exact Theory.GroupAction.ComponentRankAction.centralizer_coprime B hz hr hG
  apply Theory.GroupAction.ComponentRankAction.prime_element_mem_of_image_mem f hk B x hx
  let q := QuotientGroup.mk' (MulAut.innerSubgroup B)
  have hinner : f x ∈ MulAut.innerSubgroup B := by
    apply (QuotientGroup.eq_one_iff _).mp
    obtain ⟨k, hk⟩ := hout (q (f x))
    have hp : q (f x) ^ p = 1 := by
      rw [← map_pow, ← map_pow, ← hx, pow_orderOf_eq_one, map_one, map_one]
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      ((Nat.coprime_two_left.mpr ho).pow_left k)
      (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one hp))
  obtain ⟨b, hb⟩ := hinner
  exact mem_map.mpr ⟨b, b.property, (MulAut.conjNormal_val).trans hb⟩

/-- The same absorption statement on a literal C-component two-core quotient. -/
theorem prime_actor_mem_of_twoCore_full_rank (B : Subgroup G) [B.Normal]
    (hB : B.IsCComponent)
    (hz : Nat.Coprime p (Nat.card (center (B ⧸ pCore 2 B))))
    (hr : 2 ≤ primeRank p B) (hG : primeRank p G ≤ 2)
    (ho : Odd p) (hout : IsPGroup 2 (MulAut.Outer (B ⧸ pCore 2 B)))
    (x : G) (hx : orderOf x = p) : x ∈ B := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let I := B.map q
  let e : I ≃* B ⧸ pCore 2 B := (cComponentTwoCoreQuotientEquiv hB).symm
  let : I.Normal := (inferInstance : B.Normal).map q (QuotientGroup.mk'_surjective _)
  have hk : Nat.Coprime p (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    rw [hk]
    exact (Nat.coprime_two_right.mpr ho).pow_right k
  apply Theory.GroupAction.ComponentRankAction.prime_element_mem_of_image_mem q hk B x hx
  by_cases hqx : q x = 1
  · exact hqx ▸ I.one_mem
  have hxq : orderOf (q x) = p := by
    apply orderOf_eq_prime
    · rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
    · exact hqx
  apply prime_actor_mem_of_full_rank I ?_ ?_ ?_ ho ?_ (q x) hxq
  · rwa [Nat.card_congr (centerCongr e).toEquiv]
  · rw [primeRank_congr p e, primeRank_quotient_eq_of_isTwoGroup p ho _ pCore_isPGroup]
    exact hr
  · exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans hG
  · exact hout.of_equiv (MulAut.outerCongr e).symm

/-- An actual outside actor excludes rank two on the original C-component. -/
theorem rank_le_one_of_outside_prime_actor (B : Subgroup G) [B.Normal]
    (hB : B.IsCComponent)
    (hz : Nat.Coprime p (Nat.card (center (B ⧸ pCore 2 B))))
    (hG : primeRank p G ≤ 2) (ho : Odd p)
    (hout : IsPGroup 2 (MulAut.Outer (B ⧸ pCore 2 B)))
    (x : G) (hx : orderOf x = p) (hxn : x ∉ B) : primeRank p B ≤ 1 := by
  by_contra hn
  exact hxn (prime_actor_mem_of_twoCore_full_rank B hB hz (by omega) hG ho hout x hx)
end Theory.GroupTheory.CComponentPrimeRank
