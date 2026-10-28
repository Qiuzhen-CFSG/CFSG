module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry
public import CFSG.Quasithin.ChapterF.Section09.Basic

/-!
# The index-two coset detected by the source U action

The image of T on V has order eight and that of U has order four.
Passing through the actual conjugation map identifies its inverse image
with U C_T(V), so this is precisely the index-two subgroup of 15.3.56.

Source: Aschbacher–Smith, 15.3.51(2a), 15.3.56 and 15.3.58(3).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
variable {G : Type*} [Group G] [Finite G]

theorem sylow_span_centralizer_index (d : CharacteristicTwo.LocalData G)
    (U : Subgroup G) (hUT : U ≤ (d.T : Subgroup G))
    (hcard : Nat.card (d.action.image U) = 4) :
    ((U ⊔ ((d.T : Subgroup G) ⊓ centralizer (d.V : Set G))).subgroupOf
      (d.T : Subgroup G)).index = 2 := by
  let f : (d.T : Subgroup G) →* OrthogonalActor :=
    d.action.actor.comp (inclusion d.sylow_le)
  let UT := U.subgroupOf (d.T : Subgroup G)
  have hmap : UT.map f = d.action.image U := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t,d.sylow_le t.property⟩,ht,rfl⟩
    · rintro ⟨u,hu,rfl⟩
      exact ⟨⟨u,hUT hu⟩,hu,rfl⟩
  have hrange : f.range = d.action.image d.T := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨⟨t,d.sylow_le t.property⟩,t.property,rfl⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t,ht⟩,rfl⟩
  have hker : f.ker = (centralizer (d.V : Set G)).subgroupOf (d.T : Subgroup G) := by
    ext t
    change d.action.actor ⟨t,d.sylow_le t.property⟩=1 ↔ _
    change (⟨t,d.sylow_le t.property⟩ : d.M) ∈ d.action.actor.ker ↔ _
    rw [d.action.ker_actor]
    rfl
  have hpre : (U ⊔ ((d.T : Subgroup G) ⊓ centralizer (d.V : Set G))).subgroupOf
      (d.T : Subgroup G) = UT ⊔ f.ker := by
    rw [subgroupOf_sup hUT inf_le_left,hker]
    congr 1
    ext t
    exact ⟨fun h => h.2,fun h => ⟨t.property,h⟩⟩
  have hi := relIndex_map_map f UT ⊤
  rw [← MonoidHom.range_eq_map,top_sup_eq,relIndex_top_right] at hi
  rw [hpre,←hi,hmap,hrange]
  have hle : d.action.image U ≤ d.action.image d.T := map_mono (comap_mono hUT)
  have hh := ((d.action.image U).subgroupOf (d.action.image d.T)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,hcard] at hh
  have htcard : Nat.card (d.action.image d.T) = 8 :=
    OrthogonalGeometry.sylow_card (d.action.sylowImage d.T d.sylow_le)
  rw [htcard] at hh
  change 4 * (d.action.image U).relIndex (d.action.image d.T) = 8 at hh
  omega

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
