module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic

/-!
# Ambient subgroup transport under an isomorphism of overgroups

An isomorphism N≃N′ transports H≤N through its literal subgroupOf and then
the target subtype. Injectivity preserves membership and intersections;
commutator functoriality preserves commutator subgroups. Normalizing,
centralizing and conjugate-membership tests therefore transport without
replacing either ambient group by an abstract model.

Application: Aschbacher, *Sporadic Groups* (1994),45.11,p248.
-/

public section
open Subgroup
namespace Theory.GroupTheory.SubgroupTransport
variable {G G' : Type*} [Group G] [Group G'] {N : Subgroup G} {N' : Subgroup G'}
  (e : N ≃* N')

@[expose] def ambientHom : N →* G' := N'.subtype.comp e.toMonoidHom
@[expose] def image (H : Subgroup G) : Subgroup G' := (H.subgroupOf N).map (ambientHom e)

theorem ambientHom_injective : Function.Injective (ambientHom e) :=
  N'.subtype_injective.comp e.injective

theorem image_le (H : Subgroup G) : image e H≤N' := by
  rw [image,ambientHom,←map_map]
  exact map_subtype_le _

theorem mem_image_iff (H : Subgroup G) (x : N) : ((e x:N'):G')∈image e H ↔ (x:G)∈H := by
  constructor
  · rintro ⟨y,hy,he⟩
    exact (ambientHom_injective e he) ▸ hy
  · intro hx
    exact ⟨x,hx,rfl⟩

theorem image_eq_of_internal_eq {H : Subgroup G} {H' : Subgroup G'} (hH' : H'≤N')
    (he : (H.subgroupOf N).map e.toMonoidHom=H'.subgroupOf N') : image e H=H' := by
  rw [image,ambientHom,←map_map,he,map_subgroupOf_eq_of_le hH']

theorem image_subgroupOf (H : Subgroup G) :
    (image e H).subgroupOf N'=(H.subgroupOf N).map e.toMonoidHom := by
  apply map_injective N'.subtype_injective
  rw [map_subgroupOf_eq_of_le (image_le e H),map_map]
  rfl

theorem image_inf (H K : Subgroup G) : image e (H⊓K)=image e H⊓image e K := by
  change ((H⊓K).comap N.subtype).map (ambientHom e)=_
  rw [comap_inf,map_inf _ _ _ (ambientHom_injective e)]
  rfl

theorem subgroupOf_commutator (H K : Subgroup G) (hH : H≤N) (hK : K≤N) :
    ⁅H,K⁆.subgroupOf N=⁅H.subgroupOf N,K.subgroupOf N⁆ := by
  apply map_injective N.subtype_injective
  rw [map_subgroupOf_eq_of_le ((commutator_le_sup H K).trans (sup_le hH hK)),map_commutator,
    map_subgroupOf_eq_of_le hH,map_subgroupOf_eq_of_le hK]

theorem image_commutator (H K : Subgroup G) (hH : H≤N) (hK : K≤N) :
    image e ⁅H,K⁆=⁅image e H,image e K⁆ := by
  rw [image,subgroupOf_commutator H K hH hK,map_commutator]
  rfl

theorem image_zpowers (x : N) : image e (zpowers (x:G))=zpowers ((e x:N'):G') := by
  have hh : (zpowers (x:G)).subgroupOf N=zpowers x := by
    apply map_injective N.subtype_injective
    rw [map_subgroupOf_eq_of_le (zpowers_le.mpr x.property),MonoidHom.map_zpowers]
    rfl
  rw [image,hh,MonoidHom.map_zpowers]
  rfl

theorem normalizes_iff (H : Subgroup G) (hH : H≤N) (x : N) :
    (x:G)∈normalizer (H:Set G) ↔ ((e x:N'):G')∈normalizer (image e H:Set G') := by
  change x∈(normalizer (H:Set G)).subgroupOf N ↔ e x∈(normalizer (image e H:Set G')).subgroupOf N'
  rw [subgroupOf_normalizer_eq hH,subgroupOf_normalizer_eq (image_le e H),image_subgroupOf,
    ←map_equiv_normalizer_eq]
  simp only [mem_map_equiv,MulEquiv.symm_apply_apply]

theorem centralizes_iff (H : Subgroup G) (hH : H≤N) (x : N) :
    (x:G)∈Subgroup.centralizer (H:Set G) ↔ ((e x:N'):G')∈Subgroup.centralizer (image e H:Set G') := by
  constructor
  · intro hx y hy
    obtain ⟨t,ht,rfl⟩ := hy
    have hc : t*x=x*t := Subtype.ext (hx t ht)
    simpa only [map_mul,ambientHom,MonoidHom.comp_apply,Subgroup.subtype_apply,MulEquiv.coe_toMonoidHom] using congrArg (ambientHom e) hc
  · intro hx y hy
    let t : N := ⟨y,hH hy⟩
    have hh := hx (ambientHom e t) ⟨t,hy,rfl⟩
    change ambientHom e t*ambientHom e x=ambientHom e x*ambientHom e t at hh
    have he : t*x=x*t := ambientHom_injective e (by simpa only [map_mul] using hh)
    exact congrArg Subtype.val he

theorem conjugate_mem_iff (H : Subgroup G) (x k : N) :
    (k:G)⁻¹*(x:G)*(k:G)∈H ↔ ((e k:N'):G')⁻¹*((e x:N'):G')*((e k:N'):G')∈image e H := by
  have hh := mem_image_iff e H (k⁻¹*x*k)
  simpa only [map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv] using hh.symm

theorem exists_conjugate_mem_iff (H K : Subgroup G) (hK : K≤N) (x : N) :
    (∃ k∈K,k⁻¹*(x:G)*k∈H) ↔
      (∃ k'∈image e K,k'⁻¹*((e x:N'):G')*k'∈image e H) := by
  constructor
  · rintro ⟨k,hk,hmem⟩
    let kn : N := ⟨k,hK hk⟩
    exact ⟨e kn,(mem_image_iff e K kn).mpr hk,(conjugate_mem_iff e H x kn).mp hmem⟩
  · rintro ⟨k',⟨k,hk,rfl⟩,hmem⟩
    exact ⟨k,hk,(conjugate_mem_iff e H x k).mpr hmem⟩
end Theory.GroupTheory.SubgroupTransport
