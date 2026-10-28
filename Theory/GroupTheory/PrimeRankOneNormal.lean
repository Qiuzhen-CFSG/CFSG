module
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupAction.SubgroupCentralizerCongruence

/-!
# Prime-order elements in normalized subgroups at rank one

An order-p element outside a p-divisible subgroup that it normalizes would
centralize a nontrivial p-element of that subgroup, by the conjugacy-orbit
congruence. The two independent commuting elements would give rank two.
Thus every such element belongs to the subgroup. For an odd prime the
cyclic-Sylow characterization of rank one also controls the image modulo
a normal subgroup; this gives the corresponding membership in a join.

Source application: the literal quotient-action kernel in Aschbacher--Smith
14.6.15, printed p.1035.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- In prime rank at most one, a prime-order element normalizing a
p-divisible subgroup belongs to that subgroup. -/
theorem mem_of_prime_order_normalizes_of_rank_one (K : Subgroup G)
    (hK : p ∣ Nat.card K) (hr : primeRank p G ≤ 1)
    (x : G) (hx : orderOf x = p) (hn : x ∈ normalizer (K : Set G)) : x ∈ K := by
  by_contra hxK
  let E := zpowers x
  let : IsElementaryAbelian p E :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hx ▸ pow_orderOf_eq_one x)
  have hEN : E ≤ normalizer (K : Set G) := zpowers_le.mpr hn
  have hmod := card_modEq_card_inf_centralizer E K
    (IsElementaryAbelian.isPGroup p E) hEN
  have hd : p ∣ Nat.card (K ⊓ centralizer (E : Set G) : Subgroup G) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans hK.modEq_zero_nat)
  obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card' p hd
  have hyG : orderOf (y : G) = p := (Subgroup.orderOf_coe y).trans hy
  have hdis := K.disjoint_zpowers_of_prime_order_not_mem x hx hxK
  have hyE : (y : G) ∉ E := by
    intro hm
    have hyone := mem_bot.mp ((disjoint_iff.mp hdis).le ⟨y.property.1,hm⟩)
    have he : p = 1 := hyG.symm.trans (hyone ▸ orderOf_one)
    exact (Fact.out : p.Prime).ne_one he
  have hfix : E ≤ centralizer ({(y : G)} : Set G) := by
    intro e he
    exact mem_centralizer_singleton_iff.mpr (y.property.2 e he)
  have hE : Nat.card E = p ^ 1 := by rw [pow_one]; exact (Nat.card_zpowers x).trans hx
  have h := IsElementaryAbelian.primeRank_ge_of_fixed_join E y hyG hyE hfix hE
  omega

/-- A normal subgroup with p-divisible order contains every order-p
element when the ambient prime rank is at most one. -/
theorem prime_order_mem_normal_of_rank_one (K : Subgroup G) [K.Normal]
    (hK : p ∣ Nat.card K) (hr : primeRank p G ≤ 1)
    (x : G) (hx : orderOf x = p) : x ∈ K :=
  mem_of_prime_order_normalizes_of_rank_one K hK hr x hx (by
    rw [normalizer_eq_top]; exact mem_top _)
/-- An odd-prime element in J D lies in J B if B has surviving p-order
modulo J, is normal, and D has p-rank at most one. -/
theorem prime_order_mem_sup_of_rank_one_quotient
    (J D B : Subgroup G) [J.Normal] [B.Normal] (hBD : B ≤ D)
    (hp : Odd p) (hr : primeRank p D ≤ 1)
    (hB : p ∣ Nat.card (B.map (QuotientGroup.mk' J)))
    (x : G) (hx : orderOf x = p) (hm : x ∈ J ⊔ D) : x ∈ J ⊔ B := by
  let q := QuotientGroup.mk' J
  let E := D.map q
  let B' := (B.map q).subgroupOf E
  have hBE : B.map q ≤ E := map_mono hBD
  let : (B.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective J)
  have hB' : p ∣ Nat.card B' := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBE).toEquiv]
    exact hB
  let P : Sylow p D := Classical.choice inferInstance
  have hE : primeRank p E ≤ 1 := P.primeRank_le_one_of_surjective
    (P.isCyclic_of_odd_of_primeRank_le_one hp hr) (q.subgroupMap D) (q.subgroupMap_surjective D)
  have hxE : q x ∈ E := by
    change x ∈ (D.map q).comap q
    rw [comap_map_eq,QuotientGroup.ker_mk',sup_comm]
    exact hm
  let y : E := ⟨q x,hxE⟩
  have hyp : y^p = 1 := by
    apply Subtype.ext
    change (q x)^p = 1
    rw [←map_pow,←hx,pow_orderOf_eq_one,map_one]
  have hyB : y ∈ B' := by
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp (orderOf_dvd_of_pow_eq_one hyp) with h1 | hprime
    · rw [orderOf_eq_one_iff.mp h1]
      exact one_mem _
    · exact prime_order_mem_normal_of_rank_one B' hB' hE y hprime
  have hxB : x ∈ (B.map q).comap q := hyB
  rwa [comap_map_eq,QuotientGroup.ker_mk',sup_comm] at hxB
end Subgroup
