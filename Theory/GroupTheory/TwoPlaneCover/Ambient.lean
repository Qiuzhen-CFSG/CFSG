module
public import Theory.GroupAction.SubgroupConjugation
public import Theory.Frattini.OmegaProducts
/-! # Ambient conjugation of marked crossing planes
Frattini nontriviality, disjoint kernels and plane commutation transfer
through the actual normalizer action on the original subgroup.
Source application: Aschbacher--Smith 2.5.7.
-/
public section
open Subgroup
namespace Subgroup
variable {G:Type*} [Group G]
theorem frattini_subgroupOf_ne_bot {C R:Subgroup G} (hCR:C≤R) (hphi:frattini C≠⊥) :
    frattini (C.subgroupOf R)≠⊥ := by
  intro hh
  have hm:=frattini_map_equiv (subgroupOfEquivOfLe hCR)
  rw [hh,map_bot] at hm
  exact hphi hm.symm

theorem disjoint_normalizer_image {C R:Subgroup G} (x:G) (hx:x∈normalizer (R:Set G))
    (hd:Disjoint C (C.conjBy x)) :
    Disjoint (C.subgroupOf R)
      ((C.subgroupOf R).map (R.normalizerMonoidHom ⟨x,hx⟩).toMonoidHom) := by
  apply disjoint_def.mpr
  rintro _ ha ⟨b,hb,rfl⟩
  apply Subtype.ext
  exact disjoint_def.mp hd ha (show ((R.normalizerMonoidHom ⟨x,hx⟩) b:G)∈C.conjBy x from
    ⟨(b:G),hb,rfl⟩)

theorem centralizer_conjugate_of_normalizer_action
    (R:Subgroup G) (x:G) (hx:x∈normalizer (R:Set G)) (V:Subgroup R)
    (h:V.map (R.normalizerMonoidHom ⟨x,hx⟩).toMonoidHom≤centralizer (V:Set R)) :
    (V.map R.subtype).conjBy x≤centralizer (V.map R.subtype:Set G) := by
  rintro _ ⟨_,⟨a,ha,rfl⟩,rfl⟩ _ ⟨b,hb,rfl⟩
  exact congrArg Subtype.val (h (mem_map_of_mem (R.normalizerMonoidHom ⟨x,hx⟩).toMonoidHom ha) b hb)
end Subgroup
