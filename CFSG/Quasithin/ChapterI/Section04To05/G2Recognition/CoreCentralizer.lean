module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.ParabolicCore

/-!
# Self-centralization of the marked quaternion core

The two SL₂(3) factors are the centralizers of the opposite quaternion
factors inside their product. Thus the product meets C_H(Q₁Q₂) in the
common central involution, and C_H(Q₁Q₂) is a two-group of order at most
four. Choose an H-Sylow containing it. The aligned elementary eight is
self-centralizing in that Sylow and lies in Q₁Q₂, forcing C_H(Q₁Q₂) into
Q₁Q₂ and then into its center.

This uses the actual elementary-eight embedding from (G2), not an assumed
characteristic-two condition. It supplies the faithful outer action used
in ExtensionAction and its Chapter14Extension consumer. Source:
Aschbacher–Smith I.4(G1)–(G2), printed p.417; Fong–Wong §2F, pp.153–154.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)
attribute [local instance] G2ThreeConfiguration.H₁_normal G2ThreeConfiguration.H₂_normal

noncomputable def markedResidual :
    QuaternionResidualCentralProduct (quaternionCore c) (quaternionCoreData c) where
  left := c.H₁
  right := c.H₂
  left_model := c.H₁_model
  right_model := c.H₂_model
  left_contains := by
    change ((c.H₁.pCoreIn 2).subgroupOf (quaternionCore c)).map _ ≤ _
    rw [map_subgroupOf_eq_of_le (show c.H₁.pCoreIn 2 ≤ quaternionCore c from le_sup_left)]
    exact c.H₁.pCoreIn_le 2
  right_contains := by
    change ((c.H₂.pCoreIn 2).subgroupOf (quaternionCore c)).map _ ≤ _
    rw [map_subgroupOf_eq_of_le (show c.H₂.pCoreIn 2 ≤ quaternionCore c from le_sup_right)]
    exact c.H₂.pCoreIn_le 2
  left_core := by
    change c.H₁.pCoreIn 2 = ((c.H₁.pCoreIn 2).subgroupOf (quaternionCore c)).map _
    rw [map_subgroupOf_eq_of_le (show c.H₁.pCoreIn 2 ≤ quaternionCore c from le_sup_left)]
  right_core := by
    change c.H₂.pCoreIn 2 = ((c.H₂.pCoreIn 2).subgroupOf (quaternionCore c)).map _
    rw [map_subgroupOf_eq_of_le (show c.H₂.pCoreIn 2 ≤ quaternionCore c from le_sup_right)]
  commute := c.commute
  intersection := (quaternionCore_center c).symm
  span := (H_residual c).symm

theorem residual_core_centralizer :
    (c.H₁ ⊔ c.H₂) ⊓ centralizer (quaternionCore c : Set c.H) = c.H₁ ⊓ c.H₂ := by
  have hh := (markedResidual c).centralizer_descriptions
  have hleft : c.H₁ = (c.H₁ ⊔ c.H₂) ⊓ centralizer (c.H₂.pCoreIn 2 : Set c.H) := by
    simpa only [markedResidual,H_residual,quaternionCoreData,
      map_subgroupOf_eq_of_le (show c.H₂.pCoreIn 2 ≤ quaternionCore c from le_sup_right)] using hh.1
  have hright : c.H₂ = (c.H₁ ⊔ c.H₂) ⊓ centralizer (c.H₁.pCoreIn 2 : Set c.H) := by
    simpa only [markedResidual,H_residual,quaternionCoreData,
      map_subgroupOf_eq_of_le (show c.H₁.pCoreIn 2 ≤ quaternionCore c from le_sup_left)] using hh.2
  apply le_antisymm
  · intro x hx
    exact ⟨hleft ▸ ⟨hx.1,centralizer_le
      (show (c.H₂.pCoreIn 2 : Set c.H) ⊆ quaternionCore c from
        fun _ h => (le_sup_right : c.H₂.pCoreIn 2 ≤ quaternionCore c) h) hx.2⟩,
      hright ▸ ⟨hx.1,centralizer_le
      (show (c.H₁.pCoreIn 2 : Set c.H) ⊆ quaternionCore c from
        fun _ h => (le_sup_left : c.H₁.pCoreIn 2 ≤ quaternionCore c) h) hx.2⟩⟩
  · rw [← quaternionCore_center c]
    rintro x ⟨q,hq,rfl⟩
    refine ⟨?_,?_⟩
    · exact (sup_le (c.H₁.pCoreIn_le 2 |>.trans le_sup_left)
        (c.H₂.pCoreIn_le 2 |>.trans le_sup_right)) q.property
    · intro y hy
      exact congrArg Subtype.val (mem_center_iff.mp hq ⟨y,hy⟩)

theorem core_centralizer_is_two_group : IsPGroup 2 (centralizer (quaternionCore c : Set c.H)) := by
  let C := centralizer (quaternionCore c : Set c.H)
  let K := c.H₁ ⊔ c.H₂
  have hCK : Nat.card (K.subgroupOf C) = 2 := by
    rw [← card_map_of_injective C.subtype_injective,subgroupOf_map_subtype]
    change Nat.card ((c.H₁ ⊔ c.H₂) ⊓ centralizer (quaternionCore c : Set c.H) : Subgroup c.H) = 2
    rw [residual_core_centralizer c,intersection_card c]
  have hd : K.relIndex C ∣ 2 := by
    simpa only [K,c.index] using K.relIndex_dvd_index_of_normal C
  have hc : Nat.card C ∣ 4 := by
    have hh := (K.subgroupOf C).card_mul_index
    rw [hCK] at hh
    change 2 * K.relIndex C = Nat.card C at hh
    rw [← hh]
    exact Nat.mul_dvd_mul_left 2 hd
  exact IsPGroup.of_card_dvd_pow (n := 2) hc

theorem core_self_centralizing :
    centralizer (quaternionCore c : Set c.H) ≤ quaternionCore c := by
  obtain ⟨T,hCT⟩ := (core_centralizer_is_two_group c).exists_le_sylow
  obtain ⟨E,_,_,_,hEQ,_,hcent,_,_,_⟩ := exists_seed_in_quaternionCore c T
  intro x hx
  exact hEQ (hcent ▸ ⟨hCT hx,centralizer_le (show (E : Set c.H) ⊆ quaternionCore c from hEQ) hx⟩)

theorem core_centralizer :
    centralizer (quaternionCore c : Set c.H) = c.H₁ ⊓ c.H₂ := by
  rw [← quaternionCore_center c]
  apply le_antisymm
  · intro x hx
    exact ⟨⟨x,core_self_centralizing c hx⟩,mem_center_iff.mpr
      (fun y => Subtype.ext (hx y y.property)),rfl⟩
  · rintro x ⟨q,hq,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hq ⟨y,hy⟩)

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
