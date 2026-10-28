module

public import Theory.Frattini.Intersection
public import Theory.GroupTheory.ConjugateSpanOrder
/-!
# Ambient images under an automorphism of a subgroup

An automorphism of S transports each subgroup X≤S inside the original
ambient group. Its restriction supplies the exact group equivalence,
normalizer transport and equality of the embedded Frattini subgroups.
The final lemma shows that simultaneous normalization of a seed and its
actors normalizes the generated conjugate span. These are the literal
subgroup transports in Campbell II.6.1–2; no ambient automorphism extension
is assumed.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

@[expose] def automorphismImage (S : Subgroup G) (a : MulAut S) (X : Subgroup G) : Subgroup G :=
  ((X.subgroupOf S).map a.toMonoidHom).map S.subtype

theorem automorphismImage_le (S : Subgroup G) (a : MulAut S) (X : Subgroup G) :
    automorphismImage S a X ≤ S := by
  exact (map_le_range _ _).trans (by rw [range_subtype])

theorem automorphismImage_mono (S : Subgroup G) (a : MulAut S)
    {X Y : Subgroup G} (hXY : X ≤ Y) : automorphismImage S a X ≤ automorphismImage S a Y :=
  map_mono (map_mono (comap_mono hXY))

@[expose] noncomputable def automorphismImageEquiv (S : Subgroup G) (a : MulAut S)
    (X : Subgroup G) (hXS : X ≤ S) : X ≃* automorphismImage S a X :=
  ((subgroupOfEquivOfLe hXS).symm.trans
    ((X.subgroupOf S).equivMapOfInjective a.toMonoidHom a.injective)).trans
      (((X.subgroupOf S).map a.toMonoidHom).equivMapOfInjective S.subtype S.subtype_injective)

theorem automorphismImageEquiv_apply (S : Subgroup G) (a : MulAut S)
    (X : Subgroup G) (hXS : X ≤ S) (x : X) :
    (automorphismImageEquiv S a X hXS x : G) = (a ⟨x,hXS x.property⟩ : G) := rfl

theorem automorphismImage_symm (S : Subgroup G) (a : MulAut S)
    (X : Subgroup G) (hXS : X ≤ S) :
    automorphismImage S a.symm (automorphismImage S a X)=X := by
  unfold automorphismImage subgroupOf
  rw [comap_map_eq_self_of_injective S.subtype_injective, map_map]
  have he : a.symm.toMonoidHom.comp a.toMonoidHom = MonoidHom.id S := by
    apply MonoidHom.ext
    intro x
    exact a.symm_apply_apply x
  rw [map_map,MonoidHom.comp_assoc,he,MonoidHom.comp_id,map_comap_eq_self]
  simpa only [range_subtype] using hXS

theorem le_normalizer_automorphismImage (S : Subgroup G) (a : MulAut S)
    (X : Subgroup G) (hXS : X ≤ S) (hXN : S ≤ normalizer (X : Set G)) :
    S ≤ normalizer (automorphismImage S a X : Set G) := by
  let : (X.subgroupOf S).Normal := (normal_subgroupOf_iff_le_normalizer hXS).mpr hXN
  let : ((X.subgroupOf S).map a.toMonoidHom).Normal := Subgroup.Normal.map inferInstance a.toMonoidHom a.surjective
  have hn : (⊤ : Subgroup S) ≤ normalizer (((X.subgroupOf S).map a.toMonoidHom) : Set S) :=
    le_normalizer_of_normal
  have hm := (map_mono (f := S.subtype) hn).trans (le_normalizer_map S.subtype)
  simpa only [automorphismImage,←MonoidHom.range_eq_map,range_subtype] using hm

theorem frattini_automorphismImage (S : Subgroup G) (a : MulAut S)
    (X : Subgroup G) (hXS : X ≤ S) :
    (frattini (automorphismImage S a X)).map (automorphismImage S a X).subtype =
      automorphismImage S a ((frattini X).map X.subtype) := by
  have hSX : (X.subgroupOf S).map S.subtype = X := by
    exact map_subgroupOf_eq_of_le hXS
  have hp := frattini_image_map (X.subgroupOf S) S.subtype S.subtype_injective
  rw [hSX] at hp
  have hc : ((frattini X).map X.subtype).subgroupOf S =
      (frattini (X.subgroupOf S)).map (X.subgroupOf S).subtype := by
    rw [hp]
    exact comap_map_eq_self_of_injective S.subtype_injective _
  unfold automorphismImage
  rw [frattini_image_map _ _ S.subtype_injective,frattini_image_map _ _ a.injective,hc]

theorem normalizer_inf_le_normalizer_conjugateSpan (X K : Subgroup G) :
    normalizer (X : Set G) ⊓ normalizer (K : Set G) ≤
      normalizer (conjugateSpanBy X K : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro s hs x ⟨k,hk,t,ht,rfl⟩
  apply subset_closure
  refine ⟨s*k*s⁻¹,(mem_normalizer_iff.mp hs.2 k).mp hk,
    s*t*s⁻¹,(mem_normalizer_iff.mp hs.1 t).mp ht,?_⟩
  group
end Subgroup
