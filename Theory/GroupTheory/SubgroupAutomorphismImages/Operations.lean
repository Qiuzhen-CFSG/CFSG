module

public import Theory.GroupTheory.SubgroupAutomorphismImages
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Operations under a subgroup automorphism

The literal ambient image under an automorphism of S preserves commutators,
joins and relative centralizers when the relevant subgroups lie in S.
No extension to an automorphism of the ambient group is used. These
identities transport the mixed words in Campbell II.6.4.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

theorem automorphismImage_commutator (S : Subgroup G) (a : MulAut S)
    (X Y : Subgroup G) (hX : X ≤ S) (hY : Y ≤ S) :
    automorphismImage S a ⁅X,Y⁆ = ⁅automorphismImage S a X,automorphismImage S a Y⁆ := by
  have hm : ⁅X.subgroupOf S,Y.subgroupOf S⁆.map S.subtype = ⁅X,Y⁆ := by
    rw [map_commutator,map_subgroupOf_eq_of_le hX,map_subgroupOf_eq_of_le hY]
  have hs : ⁅X,Y⁆.subgroupOf S = ⁅X.subgroupOf S,Y.subgroupOf S⁆ := by
    rw [←hm]
    exact comap_map_eq_self_of_injective S.subtype_injective _
  unfold automorphismImage
  rw [hs,map_commutator,map_commutator]

theorem automorphismImage_bot (S : Subgroup G) (a : MulAut S) :
    automorphismImage S a ⊥ = ⊥ := by
  simp [automorphismImage,subgroupOf]

theorem automorphismImage_sup (S : Subgroup G) (a : MulAut S)
    (X Y : Subgroup G) (hX : X ≤ S) (hY : Y ≤ S) :
    automorphismImage S a (X ⊔ Y) = automorphismImage S a X ⊔ automorphismImage S a Y := by
  unfold automorphismImage
  rw [subgroupOf_sup hX hY,map_sup,map_sup]

theorem automorphismImage_inf_centralizer (S : Subgroup G) (a : MulAut S)
    (X Y : Subgroup G) (hY : Y ≤ S) :
    automorphismImage S a (X ⊓ centralizer (Y : Set G)) =
      automorphismImage S a X ⊓ centralizer (automorphismImage S a Y : Set G) := by
  apply le_antisymm
  · refine le_inf (automorphismImage_mono S a inf_le_left) ?_
    rintro z ⟨z',⟨x,hx,rfl⟩,rfl⟩ y ⟨y',⟨t,ht,rfl⟩,rfl⟩
    have hh : t*x=x*t := Subtype.ext (hx.2 t ht)
    exact congrArg Subtype.val (by simpa only [map_mul] using congrArg a hh)
  · rintro z ⟨⟨z',⟨x,hx,rfl⟩,rfl⟩,hc⟩
    refine ⟨a x,⟨x,⟨hx,?_⟩,rfl⟩,rfl⟩
    intro t ht
    let t' : S := ⟨t,hY ht⟩
    have hh := hc (a t') (mem_map_of_mem S.subtype (mem_map_of_mem a.toMonoidHom ht))
    have hh' : a t'*a x=a x*a t' := Subtype.ext hh
    have he : t'*x=x*t' := a.injective (by simpa only [map_mul] using hh')
    exact congrArg Subtype.val he

theorem automorphismImage_le_centralizer (S : Subgroup G) (a : MulAut S)
    (X Y : Subgroup G) (hc : X ≤ centralizer (Y : Set G)) :
    automorphismImage S a X ≤ centralizer (automorphismImage S a Y : Set G) := by
  rintro z ⟨z',⟨x,hx,rfl⟩,rfl⟩ y ⟨y',⟨t,ht,rfl⟩,rfl⟩
  have hh : t*x=x*t := Subtype.ext (hc hx t ht)
  exact congrArg Subtype.val (by simpa only [map_mul] using congrArg a hh)
end Subgroup
