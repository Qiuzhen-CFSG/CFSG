module

public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.CyclicSubgroupNormalizer
public import Theory.SpecificGroups.HeisenbergPrime
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Rank and cubic elements in an extraspecial centralizer

A noncentral element of order three in a subgroup P generates a cubic
subgroup disjoint from every subgroup centralizing P. Their commuting
product adds ranks, so ambient three-rank at most two bounds that
centralizing subgroup by one. The Heisenberg group supplies such an element.

When P is normal extraspecial and its center belongs to this centralizer,
every cubic element of the centralizer belongs to Z(P): its join with Z(P)
is a three-group of rank at most one, hence cyclic with a unique cubic line.
This is the centralizer step of Aschbacher--Smith15.2.3(1)(ii), p.1105.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A noncentral cubic contributes an independent direction to a centralizer. -/
theorem primeRank_le_one_of_centralizes_noncentral_cubic
    (P C : Subgroup G) (hC : C ≤ centralizer (P : Set G))
    (hr : primeRank 3 G ≤ 2) (x : P) (hx : orderOf x = 3)
    (hxZ : x ∉ center P) : primeRank 3 C ≤ 1 := by
  let A := zpowers (x : G)
  have hxC : (x : G) ∉ C := by
    intro hxC
    apply hxZ
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hC hxC y y.property)
  have hxo : orderOf (x : G) = 3 := (orderOf_coe x).trans hx
  have hd : Disjoint A C := (C.disjoint_zpowers_of_prime_order_not_mem x hxo hxC).symm
  have hac : A ≤ centralizer (C : Set G) :=
    (zpowers_le.mpr x.property).trans (le_centralizer_iff.mp hC)
  have hAr : 1 ≤ primeRank 3 A := by
    by_contra h
    have hz : primeRank 3 A = 0 := by omega
    apply (PrimeRank.eq_zero_iff_not_dvd_card.mp hz)
    rw [Nat.card_zpowers, hxo]
  have he := primeRank_sup_eq_add_of_disjoint_commuting A C hd hac 3
  have hle := (primeRank_le_of_injective 3 (A ⊔ C).subtype (A ⊔ C).subtype_injective).trans hr
  omega

/-- A subgroup centralizing Heisenberg27 has rank at most one in ambient rank two. -/
theorem primeRank_le_one_of_centralizes_heisenberg
    (P C : Subgroup G) (hC : C ≤ centralizer (P : Set G))
    (hr : primeRank 3 G ≤ 2) (e : P ≃* HeisenbergPrime 3) :
    primeRank 3 C ≤ 1 := by
  let x : P := e.symm ⟨1, 0, 0⟩
  have hxZ : x ∉ center P := by
    intro hz
    have hez : e x ∈ center (HeisenbergPrime 3) := by
      apply mem_center_iff.mpr
      intro z
      obtain ⟨y, rfl⟩ := e.surjective z
      simpa only [map_mul] using congrArg e (mem_center_iff.mp hz y)
    have hh := (HeisenbergPrime.mem_center_iff (e x)).mp hez
    have hone : (1 : ZMod 3) = 0 := by simpa only [x, e.apply_symm_apply] using hh.1
    exact one_ne_zero hone
  have hx3 : x ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, HeisenbergPrime.pow_prime (by decide), map_one]
  have hxne : x ≠ 1 := fun h => hxZ (h ▸ one_mem _)
  exact primeRank_le_one_of_centralizes_noncentral_cubic P C hC hr x
    (orderOf_eq_prime hx3 hxne) hxZ

/-- In rank one, every cubic in a centralizer lies in the central cubic line. -/
theorem cubic_mem_extraspecial_center_of_primeRank_le_one
    (P C : Subgroup G) [P.Normal] [IsExtraspecial 3 P]
    (hr : primeRank 3 C ≤ 1) (hZC : (center P).map P.subtype ≤ C)
    (x : G) (hx : x ∈ C) (hx3 : x ^ 3 = 1) :
    x ∈ (center P).map P.subtype := by
  let Z := (center P).map P.subtype
  let A := Z ⊔ zpowers x
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  have hZp : IsPGroup 3 Z := ((IsExtraspecial.isPGroup 3 P).to_subgroup (center P)).map P.subtype
  have hxp : IsPGroup 3 (zpowers x) := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one hx3)
  have hAp : IsPGroup 3 A := hZp.to_sup_of_normal_left hxp
  have hAC : A ≤ C := sup_le hZC (zpowers_le.mpr hx)
  have hAr : primeRank 3 A ≤ 1 :=
    (primeRank_le_of_injective 3 (inclusion hAC) (inclusion_injective hAC)).trans hr
  let : IsCyclic A := hAp.isCyclic_of_odd_of_elementary_card_le (by decide) (by
    intro E he
    let : IsElementaryAbelian 3 E := he
    exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hAr E)
  have hZA : Z ≤ A := le_sup_left
  have hc : Nat.card (Z.subgroupOf A) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZA).toEquiv,
      card_map_of_injective P.subtype_injective]
    exact IsExtraspecial.center_order_p 3 P
  exact mem_of_pow_card_eq_one_in_cyclic (Z.subgroupOf A)
    (x := ⟨x, (show zpowers x ≤ A from le_sup_right) (mem_zpowers x)⟩)
    (by rw [hc]; exact Subtype.ext hx3)

end Subgroup
