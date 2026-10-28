module
public import Theory.SpecificGroups.Janko3.SourceRecognition.SingerFieldAffineExtension.Extension

/-!
# Extend a new point marking from an actual affine local carrier

An initial affine marking identifies the point subgroup and full linear
complement setwise. Any new Singer marking of that same point subgroup
which preserves their actual intersection extends to the entire affine
carrier. The extension agrees pointwise and retains the full complement.
-/

public noncomputable section
namespace Sporadic.Janko3.SourceRecognition.SingerField.AffineExtension
open Subgroup Representation.CentralCubicNaturalFour
open BaumeisterParabolics
local notation "Affine" => Plane ⋊[naturalAction] LinearGroup

private theorem affine_mem_linear (x : Model) :
    affineEmbedding x ∈ (SemidirectProduct.inr : LinearGroup →* Affine).range ↔
      x ∈ pointComplement := by
  constructor
  · rintro ⟨g,hg⟩
    have hh := congrArg SemidirectProduct.left hg
    change 1 = rootCoordinates x.left at hh
    have hx : x.left = 1 := rootCoordinates.injective (hh.symm.trans (map_one _).symm)
    exact ⟨x.right,SemidirectProduct.ext hx.symm rfl⟩
  · rintro ⟨n,rfl⟩
    refine ⟨matrixEquiv n.val,?_⟩
    symm
    exact SemidirectProduct.map_inr _ _ _ n

/-- The point marking extends over a genuinely identified affine local
group, retaining its original full linear complement. -/
theorem extend_local_point_marking
    {G : Type*} [Group G] (F C : Subgroup G)
    (e₀ : G ≃* Affine)
    (hF : F.map e₀.toMonoidHom = affineEmbedding.range)
    (hC : C.map e₀.toMonoidHom =
      (SemidirectProduct.inr : LinearGroup →* Affine).range)
    (e : F ≃* Model)
    (he : ((F ⊓ C).subgroupOf F).map e.toMonoidHom = pointComplement) :
    ∃ f : G ≃* Affine,
      C.map f.toMonoidHom = (SemidirectProduct.inr : LinearGroup →* Affine).range ∧
      ∀ x : F, f x = affineEmbedding (e x) := by
  let a : F ≃* Model := ((e₀.subgroupMap F).trans (MulEquiv.subgroupCongr hF)).trans
    (MonoidHom.ofInjective affineEmbedding_injective).symm
  have ha (x : F) : affineEmbedding (a x) = e₀ x :=
    congrArg Subtype.val ((MonoidHom.ofInjective affineEmbedding_injective).apply_symm_apply
      ⟨e₀ x,hF ▸ mem_map_of_mem e₀.toMonoidHom x.property⟩)
  have hmem (x : F) : a x ∈ pointComplement ↔ (x : G) ∈ C := by
    rw [←affine_mem_linear,ha,←hC]
    constructor
    · rintro ⟨y,hy,heq⟩
      exact e₀.injective heq ▸ hy
    · intro hx
      exact mem_map_of_mem e₀.toMonoidHom hx
  have haC : ((F ⊓ C).subgroupOf F).map a.toMonoidHom = pointComplement := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (hmem x).mpr hx.2
    · intro z hz
      obtain ⟨x,rfl⟩ := a.surjective z
      exact ⟨x,⟨x.property,(hmem x).mp hz⟩,rfl⟩
  let φ : MulAut Model := a.symm.trans e
  have hφ : pointComplement.map φ.toMonoidHom = pointComplement := by
    nth_rw 1 [←haC]
    rw [map_map]
    have hh : φ.toMonoidHom.comp a.toMonoidHom = e.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      exact congrArg e (a.symm_apply_apply x)
    rw [hh,he]
  obtain ⟨Φ,hΦ,hlinear⟩ := point_automorphism_extends φ hφ
  refine ⟨e₀.trans Φ,?_,?_⟩
  · change C.map (Φ.toMonoidHom.comp e₀.toMonoidHom) = _
    rw [←map_map,hC,hlinear]
  · intro x
    change Φ (e₀ x) = _
    rw [←ha x,hΦ]
    change affineEmbedding (e (a.symm (a x))) = _
    rw [a.symm_apply_apply]
end Sporadic.Janko3.SourceRecognition.SingerField.AffineExtension
