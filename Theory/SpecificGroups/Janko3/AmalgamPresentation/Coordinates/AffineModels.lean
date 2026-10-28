module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.PairModels
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.ThirdIntersection
public import Theory.SpecificGroups.Janko3.SourceRecognition.SingerFieldAffineExtension.LocalMarking
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.SingerPointEquiv

/-!
# A common point marking for the actual first and second local groups

The literal full intersections provide the exact subgroup guards needed by
the affine extension theorem. Its new marking agrees pointwise with the
already corrected first local, while preserving the entire order-180
intersection with the third local. No compatibility is assumed for the
independent native affine coordinates.
-/

public noncomputable section
namespace Sporadic.Janko3.AmalgamPresentation.ModelCoordinates
open NineCoordinates (thirdLocalModel)
open Subgroup SourceRecognition Representation.CentralCubicNaturalFour
local notation "M16" => Theory.PSL2.BinaryFourFieldExtension.Model
local notation "CM" => CubicNormalizerModel.Model
local notation "Affine" => Plane ⋊[naturalAction] LinearGroup

/-- The three actual local models retain every full overlap setwise, with
pointwise agreement on the first-second and first-third intersections. -/
theorem exists_canonical_affine_pair_models :
    ∃ (e₁ : firstLocalModel ≃* M16) (e₂ : secondLocalModel ≃* Affine)
      (e₃ : thirdLocalModel ≃* CM),
      ((firstLocalModel ⊓ secondLocalModel).subgroupOf firstLocalModel).map e₁.toMonoidHom =
        Seventeen.ModelAmalgam.point ∧
      ((firstLocalModel ⊓ thirdLocalModel).subgroupOf firstLocalModel).map e₁.toMonoidHom =
        Seventeen.ModelAmalgam.pair ∧
      ((firstLocalModel ⊓ thirdLocalModel).subgroupOf thirdLocalModel).map e₃.toMonoidHom =
        CubicNormalizerModel.pair ∧
      ((secondLocalModel ⊓ thirdLocalModel).subgroupOf secondLocalModel).map e₂.toMonoidHom =
        (SemidirectProduct.inr : LinearGroup →* Affine).range ∧
      ((secondLocalModel ⊓ thirdLocalModel).subgroupOf thirdLocalModel).map e₃.toMonoidHom =
        CubicNormalizerModel.thirdOverlap ∧
      NineCoordinates.cubicKernel.map e₃.toMonoidHom = CubicNormalizerModel.projection.ker ∧
      (∀ x : (firstLocalModel ⊓ secondLocalModel : Subgroup Model),
        ∃ z : Seventeen.ModelAmalgam.point,
          e₁ ⟨x,x.property.1⟩ = (z : M16) ∧
          e₂ ⟨x,x.property.2⟩ = SingerField.affineEmbedding
            (Seventeen.ModelAmalgam.SingerPoint.pointEquiv.symm z)) ∧
      ∀ x : (firstLocalModel ⊓ thirdLocalModel : Subgroup Model),
        ∃ z : Seventeen.ModelAmalgam.pair,
          e₁ ⟨x,x.property.1⟩ = (z : M16) ∧
          e₃ ⟨x,x.property.2⟩ = (CubicNormalizerModel.modelPairEquiv z : CM) := by
  obtain ⟨e₁,e₃,hpoint,hpair₁,hpair₃,hthird,hkernel,hcompat⟩ := exists_canonical_point_pair_models
  let F := (firstLocalModel ⊓ secondLocalModel).subgroupOf secondLocalModel
  let C := (secondLocalModel ⊓ thirdLocalModel).subgroupOf secondLocalModel
  let e₀ := FourCoordinates.orientedLocalEquiv
  have hF : F = FourCoordinates.localSingerWords := by
    apply map_injective secondLocalModel.subtype_injective
    rw [map_subgroupOf_eq_of_le inf_le_right,first_second_intersection_eq_singer]
  have hC : C = FourCoordinates.localLinearWords := by
    apply map_injective secondLocalModel.subtype_injective
    rw [map_subgroupOf_eq_of_le inf_le_left,NineCoordinates.second_third_intersection_eq_linear]
  have hFmap : F.map e₀.toMonoidHom = SingerField.affineEmbedding.range := by
    rw [hF]
    exact FourCoordinates.orientedLocalEquiv_singerWords
  have hCmap : C.map e₀.toMonoidHom =
      (SemidirectProduct.inr : LinearGroup →* Affine).range := by
    rw [hC]
    exact FourCoordinates.orientedLocalEquiv_linearWords
  have hpointFull : ((firstLocalModel ⊓ secondLocalModel).subgroupOf firstLocalModel).map
      e₁.toMonoidHom = Seventeen.ModelAmalgam.point := by
    have hh : (firstLocalModel ⊓ secondLocalModel).subgroupOf firstLocalModel =
        SixteenCoordinates.localPointWords := by
      apply map_injective firstLocalModel.subtype_injective
      rw [map_subgroupOf_eq_of_le inf_le_left,first_second_intersection_eq_point]
    rw [hh,hpoint]
  let r : (firstLocalModel ⊓ secondLocalModel : Subgroup Model) ≃*
      Seventeen.ModelAmalgam.point :=
    (subgroupOfEquivOfLe inf_le_left).symm.trans
      ((e₁.subgroupMap ((firstLocalModel ⊓ secondLocalModel).subgroupOf firstLocalModel)).trans
        (MulEquiv.subgroupCongr hpointFull))
  let e : F ≃* SingerField.Model := (subgroupOfEquivOfLe inf_le_right).trans
    (r.trans Seventeen.ModelAmalgam.SingerPoint.pointEquiv.symm)
  have hsp (q : SingerField.Model) :
      Seventeen.ModelAmalgam.SingerPoint.pointEquiv q ∈ Seventeen.ModelAmalgam.C ↔
        q ∈ BaumeisterParabolics.pointComplement := by
    rw [←Seventeen.ModelAmalgam.SingerPoint.pointEquiv_complement]
    constructor
    · rintro ⟨v,hv,hv₁⟩
      exact Seventeen.ModelAmalgam.SingerPoint.pointEquiv.injective hv₁ ▸ hv
    · intro hq
      exact mem_map_of_mem _ hq
  have hmem (x : F) : e x ∈ BaumeisterParabolics.pointComplement ↔ (x : secondLocalModel) ∈ C := by
    rw [←hsp]
    change Seventeen.ModelAmalgam.SingerPoint.pointEquiv
      (Seventeen.ModelAmalgam.SingerPoint.pointEquiv.symm (r ⟨x,x.property⟩)) ∈
        Seventeen.ModelAmalgam.C ↔ _
    rw [Seventeen.ModelAmalgam.SingerPoint.pointEquiv.apply_symm_apply]
    change (e₁ ⟨x,x.property.1⟩ ∈ Seventeen.ModelAmalgam.point ∧
      e₁ ⟨x,x.property.1⟩ ∈ Seventeen.ModelAmalgam.pair) ↔ _
    have hp : e₁ ⟨x,x.property.1⟩ ∈ Seventeen.ModelAmalgam.point := (r ⟨x,x.property⟩).property
    rw [and_iff_right hp,←hpair₁]
    constructor
    · rintro ⟨u,hu,hu₁⟩
      have hx : u = ⟨x,x.property.1⟩ := e₁.injective hu₁
      have ht : ((x : secondLocalModel) : Model) ∈ thirdLocalModel := by
        have hh := hu.2
        change (u : Model) ∈ thirdLocalModel at hh
        rw [congrArg Subtype.val hx] at hh
        exact hh
      exact ⟨x.val.property,ht⟩
    · intro hx
      exact mem_map_of_mem e₁.toMonoidHom ⟨x.property.1,hx.2⟩
  have he : ((F ⊓ C).subgroupOf F).map e.toMonoidHom = BaumeisterParabolics.pointComplement := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (hmem x).mpr hx.2
    · intro q hq
      obtain ⟨x,rfl⟩ := e.surjective q
      exact ⟨x,⟨x.property,(hmem x).mp hq⟩,rfl⟩
  obtain ⟨e₂,hC₂,hpointcompat⟩ := SingerField.AffineExtension.extend_local_point_marking
    F C e₀ hFmap hCmap e he
  have hthirdFull : ((secondLocalModel ⊓ thirdLocalModel).subgroupOf thirdLocalModel).map
      e₃.toMonoidHom = CubicNormalizerModel.thirdOverlap := by
    have hh : (secondLocalModel ⊓ thirdLocalModel).subgroupOf thirdLocalModel =
        NineCoordinates.thirdOverlapWords := by
      apply map_injective thirdLocalModel.subtype_injective
      rw [map_subgroupOf_eq_of_le inf_le_right,NineCoordinates.thirdOverlapWords_ambient]
    rw [hh,hthird]
  refine ⟨e₁,e₂,e₃,hpointFull,hpair₁,hpair₃,hC₂,hthirdFull,hkernel,?_,hcompat⟩
  intro x
  refine ⟨r x,rfl,?_⟩
  exact hpointcompat ⟨⟨x,x.property.2⟩,x.property⟩
end Sporadic.Janko3.AmalgamPresentation.ModelCoordinates
