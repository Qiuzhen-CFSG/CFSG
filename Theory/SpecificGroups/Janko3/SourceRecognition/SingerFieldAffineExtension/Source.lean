module
public import Theory.SpecificGroups.Janko3.SourceRecognition.SingerFieldAffineExtension.Extension
public import Theory.SpecificGroups.Janko3.SourceRecognition.PlaneFieldCompatibility

/-!
# Extend an actual marking of the original order-480 intersection

An isomorphism on the same original field subgroup need only retain its
literal order-thirty complement. The proved field-point extension then
constructs a marking of the entire original affine normalizer with exact
pointwise agreement and the original full order-180 complement retained.
No compatibility equation on an arbitrarily supplied affine map is assumed.
-/

public noncomputable section
namespace Sporadic.Janko3.SourceRecognition.PlaneTransport
open Subgroup
open Representation.CentralCubicNaturalFour
open SingerField hiding normalizer
open BaumeisterParabolics

/-- Any marking of the original point subgroup preserving its actual
order-thirty overlap extends to the full original affine normalizer. -/
theorem affine_equiv_extending_original_point_marking
    {G : Type*} [Group G]
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (hC : (A.subgroupOf (normalizer (A : Set G))).IsComplement' C)
    (ha : ∀ (c : C) (x : A),
      a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j : Model →* G) (hj : FieldEmbedding A C a j)
    (e : j.range ≃* Model)
    (he : ((overlap j).subgroupOf j.range).map e.toMonoidHom = pointComplement) :
    ∃ f : normalizer (A : Set G) ≃* Plane ⋊[naturalAction] LinearGroup,
      C.map f.toMonoidHom =
        (SemidirectProduct.inr : LinearGroup →* Plane ⋊[naturalAction] LinearGroup).range ∧
      ∀ x : j.range, f ⟨x,hj.2.1 x.property⟩ = affineEmbedding (e x) := by
  let b := MonoidHom.ofInjective hj.1
  let φ : MulAut Model := b.trans e
  have hb : pointComplement.map b.toMonoidHom = (overlap j).subgroupOf j.range := by
    apply map_injective j.range.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le (overlap_le j)]
    rfl
  have hc : pointComplement.map φ.toMonoidHom = pointComplement := by
    change pointComplement.map (e.toMonoidHom.comp b.toMonoidHom) = _
    rw [←map_map,hb,he]
  obtain ⟨Φ,hΦ,hL⟩ := SingerField.AffineExtension.point_automorphism_extends φ hc
  obtain ⟨f₀,_hA,hC₀,hj₀⟩ := affine_equiv_preserving_fieldEmbedding A C l a hC ha j hj
  have hCmap : C.map f₀.toMonoidHom =
      (SemidirectProduct.inr : LinearGroup →* Plane ⋊[naturalAction] LinearGroup).range := by
    apply le_antisymm
    · rintro _ ⟨c,hc,rfl⟩
      exact ⟨l ⟨c,hc⟩,(hC₀ ⟨c,hc⟩).symm⟩
    · rintro _ ⟨d,rfl⟩
      refine ⟨l.symm d,(l.symm d).property,?_⟩
      have hh := hC₀ (l.symm d)
      rw [l.apply_symm_apply] at hh
      exact hh
  refine ⟨f₀.trans Φ,?_,?_⟩
  · change C.map (Φ.toMonoidHom.comp f₀.toMonoidHom) = _
    rw [←map_map,hCmap,hL]
  · intro x
    obtain ⟨y,rfl⟩ := b.surjective x
    change Φ (f₀ ⟨j y,hj.2.1 ⟨y,rfl⟩⟩) = affineEmbedding (φ y)
    rw [hj₀,hΦ]
end Sporadic.Janko3.SourceRecognition.PlaneTransport
