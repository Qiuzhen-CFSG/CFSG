module
public import Theory.GroupTheory.PCoreNormalizerAction
public import Theory.GroupTheory.PrimeRankResidualCentralizer
/-!
# Cubic centers fixed by normalized two-subgroups

A subgroup of three-rank two contains the cubic center of a group of
three-rank at most two. If this center lies in the core-quotient image
of K, and K normalizes a two-subgroup Q, then Q fixes the center:
the displacement of a lift lies both in the image of Q and in the
cubic center, so is trivial.

The core quotient and normalizer action are literal. This is the
rank argument used with the original QI in Aschbacher--Smith 15.2.23,
pp.1115--1117, and with the original radical in 15.3.21, p.1127.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]


/-- A rank-two subgroup contains a central cubic under the ambient rank bound. -/
theorem cubic_center_le_of_three_rank_two (K : Subgroup G)
    (hrK : 2 ≤ primeRank 3 K) (hrG : primeRank 3 G ≤ 2)
    (hc : Nat.card (center G) = 3) : center G ≤ K := by
  obtain ⟨B,hB,hBc⟩ := exists_elementaryAbelian_card_primeRank (G := K) (p := 3)
  let := hB
  let A := B.map K.subtype
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.map K.subtype
  have hr : primeRank 3 K = 2 := le_antisymm ((primeRank_subgroup_le 3 K).trans hrG) hrK
  have hAc : Nat.card A = 3^2 := by
    rw [card_map_of_injective K.subtype_injective,hBc,hr]
  intro z hz
  by_contra hzK
  have hz1 : z ≠ 1 := fun he => hzK (he ▸ K.one_mem)
  have hz3 : orderOf z = 3 := orderOf_eq_prime (by
    have h := pow_card_eq_one' (x := (⟨z,hz⟩ : center G))
    rw [hc] at h
    exact congrArg Subtype.val h) hz1
  have hfix : A ≤ centralizer ({z} : Set G) := by
    intro a _
    exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hz a)
  have hbad := IsElementaryAbelian.primeRank_ge_of_fixed_join A z hz3
    (fun h => hzK (map_subtype_le _ h)) hfix hAc
  omega

omit [Finite G] in
/-- A normalized two-subgroup fixes a cubic core center already in the image of its normalizer. -/
theorem pCoreNormalizerAction_fixes_center_of_image
    (X K Q : Subgroup G) (hKQ : K ≤ normalizer (Q : Set G))
    (hQ : IsPGroup 2 Q)
    (hc : Nat.card (center (X ⧸ pCore 2 X)) = 3)
    (himage : center (X ⧸ pCore 2 X) ≤
      (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)))
    (r : normalizer (X : Set G)) (hr : (r : G) ∈ Q)
    (z : X ⧸ pCore 2 X) (hz : z ∈ center (X ⧸ pCore 2 X)) :
    pCoreNormalizerAction 2 X r z = z := by
  let q := QuotientGroup.mk' (pCore 2 X)
  let a := X.normalizerMonoidHom r
  let b := pCoreNormalizerAction 2 X r
  obtain ⟨y,hy,hyz⟩ := himage hz
  change q y = z at hyz
  let t : X := a y * y⁻¹
  have htQ : t ∈ Q.subgroupOf X := by
    change ⁅(r : G),(y : G)⁆ ∈ Q
    exact le_normalizer_iff_commutator_le_left.mp hKQ (commutator_mem_commutator hr hy)
  have hqt : q t = b z * z⁻¹ := by
    change q (a y * y⁻¹) = b z * z⁻¹
    rw [map_mul,map_inv,←pCoreNormalizerAction_mk,hyz]
  have hcenter : q t ∈ center (X ⧸ pCore 2 X) := by
    rw [hqt]
    exact (center _).mul_mem (centerCongr b ⟨z,hz⟩).property ((center _).inv_mem hz)
  have htwo : IsPGroup 2 ((Q.subgroupOf X).map q) := hQ.comap_subtype.map q
  have hthree : IsPGroup 3 (center (X ⧸ pCore 2 X)) :=
    IsPGroup.of_card (n := 1) (by simpa using hc)
  have he : q t = 1 := disjoint_def.mp
    (htwo.disjoint_of_coprime hthree (by decide)) ⟨t,htQ,rfl⟩ hcenter
  rwa [hqt,mul_inv_eq_one] at he
end Subgroup
