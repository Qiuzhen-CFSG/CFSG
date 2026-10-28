module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Theory.GroupTheory.IndexTwoIntersection
public import Theory.GroupTheory.CommutatorOrbitCard

/-!
# A characteristic abelian sixteen in a group with small center

A group of order at most 32 with center of order four has at most one
abelian subgroup of order sixteen: two distinct such subgroups would
generate the group and make their intersection of order eight central.
Uniqueness makes this subgroup characteristic.

Source: the elementary normal-base argument in Janko–Thompson,
Math. Z. 113 (1970), 1.4 and the final paragraph of p.395.
-/

open Subgroup

public theorem Subgroup.characteristic_of_card_sixteen_of_center_card_four
    {G : Type*} [Group G] [Finite G]
    (hc : Nat.card G ≤ 32) (hz : Nat.card (center G) = 4)
    (B : Subgroup G) [IsMulCommutative B] (hb : Nat.card B = 16) :
    B.Characteristic := by
  have hi (A : Subgroup G) [IsMulCommutative A] (ha : Nat.card A = 16) :
      A.index = 2 := by
    have hm := A.card_mul_index
    rw [ha] at hm
    have hn : A.index ≠ 1 := by
      intro he
      have ht : A = ⊤ := index_eq_one.mp he
      have hg : IsMulCommutative G := isMulCommutative_iff.mpr fun x y => by
        exact A.le_centralizer (ht ▸ mem_top y) x (ht ▸ mem_top x)
      have hz' := hz
      rw [center_eq_top, card_top] at hz'
      omega
    have hp := A.index_ne_zero_of_finite
    omega
  have huniq (A : Subgroup G) [IsMulCommutative A] (ha : Nat.card A = 16) : A = B := by
    by_contra hne
    have hAi := hi A ha
    have hBi := hi B hb
    have hAB : ¬ A ≤ B := fun hle => hne (eq_of_le_of_card_ge hle (by omega))
    have hBA : ¬ B ≤ A := fun hle => hne (eq_of_le_of_card_ge hle (by omega)).symm
    have hsup : A ⊔ B = ⊤ := by
      apply index_eq_one.mp
      have hlt : A < A ⊔ B := lt_of_le_of_ne le_sup_left (fun he => hBA (he ▸ le_sup_right))
      have hh := index_strictAnti hlt
      have hp := (A ⊔ B).index_ne_zero_of_finite
      omega
    have hrel := subgroupOf_index_eq_two A B hAi hBA
    have hk := (A.subgroupOf B).card_mul_index
    rw [hrel, hb] at hk
    have hcent (x : A.subgroupOf B) : ((x : B) : G) ∈ center G := by
      apply mem_center_iff.mpr
      have hle : A ⊔ B ≤ centralizer ({((x : B) : G)} : Set G) := sup_le
        (fun a ha => mem_centralizer_singleton_iff.mpr (A.le_centralizer x.property a ha))
        (fun b hb => mem_centralizer_singleton_iff.mpr (B.le_centralizer x.val.property b hb))
      rw [hsup] at hle
      intro g
      exact mem_centralizer_singleton_iff.mp (hle (mem_top g))
    let f : A.subgroupOf B → center G := fun x => ⟨x.val.val, hcent x⟩
    have hf : Function.Injective f := by
      intro x y he
      exact Subtype.ext (Subtype.ext (congrArg (fun z : center G => (z : G)) he))
    have hh := Nat.card_le_card_of_injective f hf
    rw [hz] at hh
    omega
  apply characteristic_iff_map_eq.mpr
  intro f
  let : IsMulCommutative (B.map f.toMonoidHom) := map_isMulCommutative B _
  apply huniq
  rw [card_map_of_injective f.injective, hb]
open scoped commutatorElement

public theorem Subgroup.card_le_thirtytwo_of_center_four_selfCentralizing_eight
    {G : Type*} [Group G] [Finite G]
    (hz : Nat.card (center G) = 4) (hclass : _root_.commutator G ≤ center G)
    (A : Subgroup G) [IsMulCommutative A] (ha : Nat.card A = 8)
    (hself : centralizer (A : Set G) ≤ A) : Nat.card G ≤ 32 := by
  have hZA : center G ≤ A := (center_le_centralizer _).trans hself
  have hidx : (center G).relIndex A = 2 := by
    have h := ((center G).subgroupOf A).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hZA).toEquiv, hz, ha] at h
    change 4 * (center G).relIndex A = 8 at h
    omega
  have hnot : ¬ A ≤ center G := by
    intro hle
    have hc := card_le_of_le hle
    omega
  obtain ⟨y, hyA, hyZ⟩ := SetLike.not_le_iff_exists.mp hnot
  have hgen : center G ⊔ zpowers y = A := by
    have hle : center G ⊔ zpowers y ≤ A := sup_le hZA (zpowers_le.mpr hyA)
    have hm := relIndex_mul_relIndex (center G) (center G ⊔ zpowers y) A le_sup_left hle
    rw [hidx] at hm
    have hne : (center G).relIndex (center G ⊔ zpowers y) ≠ 1 := by
      intro h
      exact hyZ ((relIndex_eq_one.mp h) (mem_sup_right (mem_zpowers y)))
    have htwo : (center G).relIndex (center G ⊔ zpowers y) = 2 := by
      exact (Nat.prime_two.eq_one_or_self_of_dvd _ ⟨_, hm.symm⟩).resolve_left hne
    have hh : (center G ⊔ zpowers y).relIndex A = 1 := by
      rw [htwo] at hm
      omega
    exact le_antisymm hle (relIndex_eq_one.mp hh)
  have hyC : centralizer ({y} : Set G) ≤ A := by
    intro x hx
    apply hself
    have hle : A ≤ centralizer ({x} : Set G) := by
      rw [← hgen]
      refine sup_le (center_le_centralizer _) (zpowers_le.mpr ?_)
      exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp hx).symm
    intro a ha
    exact mem_centralizer_singleton_iff.mp (hle ha)
  have hc := card_le_commutator_card_mul_centralizer (⊤ : Subgroup G) y
  have hcomm : Nat.card (⁅(⊤ : Subgroup G), zpowers y⁆ : Subgroup G) ≤ 4 := by
    exact (card_le_of_le ((commutator_mono le_rfl le_top).trans hclass)).trans_eq hz
  have hcent : Nat.card ((centralizer ({y} : Set G)).subgroupOf ⊤) ≤ 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show centralizer ({y} : Set G) ≤ ⊤ from le_top)).toEquiv]
    exact (card_le_of_le hyC).trans_eq ha
  rw [card_top] at hc
  exact hc.trans (by nlinarith)
