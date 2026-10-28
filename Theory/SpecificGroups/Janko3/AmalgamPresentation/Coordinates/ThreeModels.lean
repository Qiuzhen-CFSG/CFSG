module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.AffineModels
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicNormalizerLinearMarking

/-!
# Simultaneous canonical markings of all three actual ATLAS locals

The full order-180 map is forced by its original order-thirty restriction.
Its restriction agrees with the fixed linear-to-cubic map through the
already proved point and full-pair equations. Rigidity of C3 times A5
therefore completes all three pointwise overlap identifications.
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
theorem exists_canonical_three_local_models :
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
      (∀ x : (secondLocalModel ⊓ thirdLocalModel : Subgroup Model), ∃ z : LinearGroup,
        e₂ ⟨x,x.property.1⟩ = SemidirectProduct.inr z ∧
        e₃ ⟨x,x.property.2⟩ = (CubicNormalizerModel.linearThirdEquiv z : CM)) ∧
      ∀ x : (firstLocalModel ⊓ thirdLocalModel : Subgroup Model),
        ∃ z : Seventeen.ModelAmalgam.pair,
          e₁ ⟨x,x.property.1⟩ = (z : M16) ∧
          e₃ ⟨x,x.property.2⟩ = (CubicNormalizerModel.modelPairEquiv z : CM) := by
  obtain ⟨e₁,e₂,e₃,hpoint,hpair₁,hpair₃,hlinear,hthird,hkernel,hpointcompat,hpaircompat⟩ :=
    exists_canonical_affine_pair_models
  let E := secondLocalModel ⊓ thirdLocalModel
  let e₂E : E ≃* LinearGroup :=
    (subgroupOfEquivOfLe (show E ≤ secondLocalModel from inf_le_left)).symm.trans
      (((e₂.subgroupMap (E.subgroupOf secondLocalModel)).trans (MulEquiv.subgroupCongr hlinear)).trans
        (MonoidHom.ofInjective (SemidirectProduct.inr_injective (φ := naturalAction))).symm)
  let e₃E : E ≃* CubicNormalizerModel.thirdOverlap :=
    (subgroupOfEquivOfLe (show E ≤ thirdLocalModel from inf_le_right)).symm.trans
      ((e₃.subgroupMap (E.subgroupOf thirdLocalModel)).trans (MulEquiv.subgroupCongr hthird))
  have he₂E (x : E) : e₂ ⟨x,x.property.1⟩ = SemidirectProduct.inr (e₂E x) := by
    exact (congrArg Subtype.val
      ((MonoidHom.ofInjective (SemidirectProduct.inr_injective (φ := naturalAction))).apply_symm_apply
        ⟨e₂ ⟨x,x.property.1⟩,hlinear ▸ mem_map_of_mem e₂.toMonoidHom x.property⟩)).symm
  have he₃E (x : E) : (e₃E x : CM) = e₃ ⟨x,x.property.2⟩ := rfl
  let U := firstLocalModel.subgroupOf E
  let V := ((firstLocalModel ⊓ secondLocalModel) ⊓
    (firstLocalModel ⊓ thirdLocalModel)).subgroupOf firstLocalModel
  have hUim : U.map E.subtype = (firstLocalModel ⊓ secondLocalModel) ⊓
      (firstLocalModel ⊓ thirdLocalModel) := by
    rw [subgroupOf_map_subtype]
    ext x
    exact ⟨fun h => ⟨⟨h.1,h.2.1⟩,⟨h.1,h.2.2⟩⟩,
      fun h => ⟨h.1.1,⟨h.1.2,h.2.2⟩⟩⟩
  have hVim : V.map firstLocalModel.subtype = (firstLocalModel ⊓ secondLocalModel) ⊓
      (firstLocalModel ⊓ thirdLocalModel) :=
    map_subgroupOf_eq_of_le (inf_le_left.trans inf_le_left)
  have hV : V.map e₁.toMonoidHom = Seventeen.ModelAmalgam.point ⊓ Seventeen.ModelAmalgam.pair := by
    change (((firstLocalModel ⊓ secondLocalModel).subgroupOf firstLocalModel) ⊓
      ((firstLocalModel ⊓ thirdLocalModel).subgroupOf firstLocalModel)).map e₁.toMonoidHom = _
    rw [map_inf _ _ _ e₁.injective,hpoint,hpair₁]
  have hU : Nat.card U = 30 := by
    rw [←card_map_of_injective E.subtype_injective,hUim,←hVim,
      card_map_of_injective firstLocalModel.subtype_injective,
      ←card_map_of_injective (f := e₁.toMonoidHom) e₁.injective,hV,
      Seventeen.ModelAmalgam.overlap_card]
  have hmaps : e₂E.trans CubicNormalizerModel.linearThirdEquiv = e₃E := by
    apply alternatingGroup.FiveLocalGeometry.CubicThirty.marked_equiv_ext
      (e₂E.trans Representation.SL2FourNatural.SemilinearNormalizer.cubicFiveEquiv) U hU
    intro x
    let xp : (firstLocalModel ⊓ secondLocalModel : Subgroup Model) :=
      ⟨x,⟨x.property,x.val.property.1⟩⟩
    obtain ⟨z,hz₁,hz₂⟩ := hpointcompat xp
    let xh : (firstLocalModel ⊓ thirdLocalModel : Subgroup Model) :=
      ⟨x,⟨x.property,x.val.property.2⟩⟩
    obtain ⟨w,hw₁,hw₃⟩ := hpaircompat xh
    have hzw : (z : M16) = w := hz₁.symm.trans hw₁
    have hzC : z ∈ Seventeen.ModelAmalgam.C := by
      refine ⟨z.property,?_⟩
      change (z : M16) ∈ Seventeen.ModelAmalgam.pair
      rw [hzw]
      exact w.property
    have hzmap : z ∈ BaumeisterParabolics.pointComplement.map
        Seventeen.ModelAmalgam.SingerPoint.pointEquiv.toMonoidHom :=
      Seventeen.ModelAmalgam.SingerPoint.pointEquiv_complement.symm ▸ hzC
    obtain ⟨q,hq,hqz⟩ := hzmap
    obtain ⟨n,rfl⟩ := hq
    have he₂n : e₂E x.val = SingerField.matrixEquiv n.val := by
      apply SemidirectProduct.inr_injective (φ := naturalAction)
      rw [←he₂E]
      change e₂ ⟨xp,xp.property.2⟩ = _
      rw [hz₂,←hqz]
      change SingerField.affineEmbedding
        (Seventeen.ModelAmalgam.SingerPoint.pointEquiv.symm
          (Seventeen.ModelAmalgam.SingerPoint.pointEquiv (SemidirectProduct.inr n))) = _
      rw [Seventeen.ModelAmalgam.SingerPoint.pointEquiv.symm_apply_apply]
      exact SemidirectProduct.map_inr _ _ _ n
    apply Subtype.ext
    change (CubicNormalizerModel.linearThirdEquiv (e₂E x.val) : CM) = _
    rw [he₂n,CubicNormalizerModel.linearThirdEquiv_apply,he₃E,hw₃]
    apply congrArg (fun t : Seventeen.ModelAmalgam.pair =>
      (CubicNormalizerModel.modelPairEquiv t : CM))
    apply Subtype.ext
    rw [CubicNormalizerModel.singerPair_coe]
    exact (congrArg Subtype.val hqz).trans hzw
  refine ⟨e₁,e₂,e₃,hpoint,hpair₁,hpair₃,hlinear,hthird,hkernel,hpointcompat,?_,hpaircompat⟩
  intro x
  refine ⟨e₂E x,he₂E x,?_⟩
  have hh := congrArg (fun e : E ≃* CubicNormalizerModel.thirdOverlap => (e x : CM)) hmaps
  exact hh.symm
end Sporadic.Janko3.AmalgamPresentation.ModelCoordinates
