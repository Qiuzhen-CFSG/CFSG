module

public import Stellmacher.ElementaryAbelianMaxProduct
public import Stellmacher.OmegaOneCenterMap

/-!
# Omega centers of internal direct products

Central involutions in a direct product are exactly pairs of central involutions.
Injective transport gives the identity for disjoint commuting subgroups with
their actual inclusions. This supplies the omega-center step after the elementary
Thompson product formula in Aschbacher–Smith, proof of 13.6.6, printed p.927.
-/

public section
open Subgroup
namespace Stellmacher
variable {G H : Type*} [Group G] [Group H]

theorem omegaOneCenterAmbient_prod (A : Subgroup G) (B : Subgroup H) :
    omegaOneCenterAmbient (A.prod B) =
      (omegaOneCenterAmbient A).prod (omegaOneCenterAmbient B) := by
  ext x
  simp only [mem_prod, mem_omegaOneCenterAmbient_iff]
  constructor
  · rintro ⟨⟨ha,hb⟩, hp, hc⟩
    refine ⟨⟨ha, congrArg Prod.fst hp, ?_⟩, ⟨hb, congrArg Prod.snd hp, ?_⟩⟩
    · intro a ha
      exact congrArg Prod.fst (hc (a,1) ⟨ha, B.one_mem⟩)
    · intro b hb
      exact congrArg Prod.snd (hc (1,b) ⟨A.one_mem, hb⟩)
  · rintro ⟨⟨ha,hpa,hca⟩, ⟨hb,hpb,hcb⟩⟩
    refine ⟨⟨ha,hb⟩, Prod.ext hpa hpb, ?_⟩
    rintro ⟨a,b⟩ ⟨ha,hb⟩
    exact Prod.ext (hca a ha) (hcb b hb)

private theorem map_prod_join {K : Type*} [Group K]
    (f : G × H →* K) (A : Subgroup G) (B : Subgroup H) :
    (A.prod B).map f = (A.map (f.comp (MonoidHom.inl G H))) ⊔
      (B.map (f.comp (MonoidHom.inr G H))) := by
  apply le_antisymm
  · rintro x ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    have h := (A.map (f.comp (MonoidHom.inl G H)) ⊔
      B.map (f.comp (MonoidHom.inr G H))).mul_mem
      (mem_sup_left (mem_map_of_mem _ ha)) (mem_sup_right (mem_map_of_mem _ hb))
    simpa only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
      ← map_mul, Prod.mk_mul_mk, mul_one, one_mul] using h
  · apply sup_le
    · rintro x ⟨a, ha, rfl⟩
      exact ⟨(a, 1), ⟨ha, B.one_mem⟩, rfl⟩
    · rintro x ⟨b, hb, rfl⟩
      exact ⟨(1, b), ⟨A.one_mem, hb⟩, rfl⟩

theorem omegaOneCenterAmbient_sup_of_disjoint_of_commuting
    (A B : Subgroup G) (hd : Disjoint A B) (hc : A ≤ centralizer (B : Set G)) :
    omegaOneCenterAmbient (A ⊔ B) = omegaOneCenterAmbient A ⊔ omegaOneCenterAmbient B := by
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hc
  let f := (A ⊔ B).subtype.comp e.toMonoidHom
  have hf : Function.Injective f := (A ⊔ B).subtype_injective.comp e.injective
  have hr : (⊤ : Subgroup (A × B)).map f = A ⊔ B := by
    ext x
    constructor
    · rintro ⟨a, _, rfl⟩
      exact (e a).property
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, mem_top _, congrArg Subtype.val (e.apply_symm_apply _)⟩
  have hl : f.comp (MonoidHom.inl A B) = A.subtype := by
    ext a
    exact (he a 1).trans (mul_one _)
  have hh : f.comp (MonoidHom.inr A B) = B.subtype := by
    ext b
    exact (he 1 b).trans (one_mul _)
  calc
    omegaOneCenterAmbient (A ⊔ B) = (omegaOneCenterAmbient (⊤ : Subgroup (A × B))).map f := by
      rw [← omegaOneCenterAmbient_map_injective f hf, hr]
    _ = ((omegaOneCenterAmbient (⊤ : Subgroup A)).prod
        (omegaOneCenterAmbient (⊤ : Subgroup B))).map f := by
      rw [← top_prod_top, omegaOneCenterAmbient_prod]
    _ = omegaOneCenterAmbient A ⊔ omegaOneCenterAmbient B := by
      rw [map_prod_join, hl, hh, ← omegaOneCenterAmbient_map_injective A.subtype A.subtype_injective,
        ← omegaOneCenterAmbient_map_injective B.subtype B.subtype_injective,
        ← MonoidHom.range_eq_map, ← MonoidHom.range_eq_map, range_subtype, range_subtype]
end Stellmacher
