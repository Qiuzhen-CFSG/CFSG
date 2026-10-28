module
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Mathlib.GroupTheory.Sylow

/-!
A two-group acting on an elementary four-group has image of order at most two. Any nontrivial acting subgroup therefore supplements the full centralizer. This is the cubic Sylow reduction in Aschbacher–Smith C.6.1, printed p.165.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem four_twoGroup_action_card (U P : Subgroup G) [IsKleinFour U]
    (hp : IsPGroup 2 P) (hn : P ≤ normalizer (U : Set G)) :
    Nat.card ((U.normalizerMonoidHom.comp (inclusion hn)).range) ≤ 2 := by
  let a := U.normalizerMonoidHom.comp (inclusion hn)
  have hd : Nat.card a.range ∣ 6 := by
    simpa only [IsKleinFour.card_mulAut] using a.range.card_subgroup_dvd_card
  have h2 : IsPGroup 2 a.range := hp.of_surjective a.rangeRestrict a.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have hk1 : k ≤ 1 := by
    by_contra hh
    have h4 : 4 ∣ 2 ^ k := by
      exact pow_dvd_pow 2 (by omega : 2 ≤ k)
    have : 4 ∣ 6 := h4.trans (hk ▸ hd)
    norm_num at this
  change Nat.card a.range ≤ 2
  rw [hk]
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> norm_num

theorem four_twoGroup_centralizer_supplement (U P V : Subgroup G) [IsKleinFour U]
    (hp : IsPGroup 2 P) (hn : P ≤ normalizer (U : Set G)) (hv : V ≤ P)
    (hnc : ¬ V ≤ centralizer (U : Set G)) :
    P = V ⊔ (P ⊓ centralizer (U : Set G)) := by
  let N := normalizer (U : Set G)
  let a := U.normalizerMonoidHom
  let J := (P.subgroupOf N).map a
  let B := (V.subgroupOf N).map a
  have hJ : Nat.card J ≤ 2 := by
    have he : J = (a.comp (inclusion hn)).range := by
      ext f
      constructor
      · rintro ⟨p,hp,rfl⟩
        exact ⟨⟨p,hp⟩,rfl⟩
      · rintro ⟨p,rfl⟩
        exact ⟨inclusion hn p,p.property,rfl⟩
    rw [he]
    exact four_twoGroup_action_card U P hp hn
  have hBne : B ≠ ⊥ := by
    intro he
    apply hnc
    intro v hvm
    have hh : a ⟨v,hn (hv hvm)⟩ ∈ B := mem_map_of_mem a hvm
    rw [he] at hh
    have hc : (⟨v,hn (hv hvm)⟩ : N) ∈ a.ker := hh
    rw [normalizerMonoidHom_ker] at hc
    exact hc
  have hB : 2 ≤ Nat.card B := by
    have hpos : 0 < Nat.card B := Nat.card_pos
    have hnot : Nat.card B ≠ 1 := fun he => hBne (card_eq_one.mp he)
    omega
  have he : B = J := eq_of_le_of_card_ge (map_mono (subgroupOf_mono _ hv)) (hJ.trans hB)
  apply le_antisymm
  · intro p hpm
    have hm : a ⟨p,hn hpm⟩ ∈ B := he.symm ▸ mem_map_of_mem a hpm
    obtain ⟨v,hvm,heq⟩ := hm
    have hk : v⁻¹ * (⟨p,hn hpm⟩ : N) ∈ a.ker := by
      change a _ = 1
      rw [map_mul,map_inv,heq,inv_mul_cancel]
    rw [normalizerMonoidHom_ker] at hk
    have hc : (v : G)⁻¹ * p ∈ P ⊓ centralizer (U : Set G) :=
      ⟨P.mul_mem (P.inv_mem (hv hvm)) hpm,hk⟩
    have hh : (v : G) * ((v : G)⁻¹ * p) ∈ V ⊔ (P ⊓ centralizer (U : Set G)) :=
      mul_mem_sup hvm hc
    simpa only [mul_inv_cancel_left] using hh
  · exact sup_le hv inf_le_left
end Theory.GroupTheory
