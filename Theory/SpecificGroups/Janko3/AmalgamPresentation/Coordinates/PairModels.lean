module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.PointIntersection
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.CanonicalOverlaps
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.CompatiblePairMapsForm
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.CubicPairBorelInversion

/-!
# Compatible first and third markings of the actual ATLAS local groups

The native local isomorphisms identify the full pair and third overlap.
A proved pair-automorphism extension gives pointwise agreement on every
actual common element. Its explicit inner/field form preserves the two
Borels; simultaneous cubic inversion restores the designated Borel when
necessary, while retaining the whole third overlap and cubic kernel.
-/

public noncomputable section
namespace Sporadic.Janko3.AmalgamPresentation.ModelCoordinates
open NineCoordinates (thirdLocalModel)
open Subgroup SourceRecognition
local notation "M16" => Theory.PSL2.BinaryFourFieldExtension.Model
local notation "CM" => CubicNormalizerModel.Model

/-- Actual first/third model markings agree on their entire literal
intersection and retain the other designated overlap subgroups. -/
theorem exists_canonical_point_pair_models :
    ∃ (e₁ : firstLocalModel ≃* M16) (e₃ : thirdLocalModel ≃* CM),
      SixteenCoordinates.localPointWords.map e₁.toMonoidHom = Seventeen.ModelAmalgam.point ∧
      ((firstLocalModel ⊓ thirdLocalModel).subgroupOf firstLocalModel).map e₁.toMonoidHom =
        Seventeen.ModelAmalgam.pair ∧
      ((firstLocalModel ⊓ thirdLocalModel).subgroupOf thirdLocalModel).map e₃.toMonoidHom =
        CubicNormalizerModel.pair ∧
      NineCoordinates.thirdOverlapWords.map e₃.toMonoidHom = CubicNormalizerModel.thirdOverlap ∧
      NineCoordinates.cubicKernel.map e₃.toMonoidHom = CubicNormalizerModel.projection.ker ∧
      ∀ x : (firstLocalModel ⊓ thirdLocalModel : Subgroup Model),
        ∃ z : Seventeen.ModelAmalgam.pair,
          e₁ ⟨x,x.property.1⟩ = (z : M16) ∧
          e₃ ⟨x,x.property.2⟩ = (CubicNormalizerModel.modelPairEquiv z : CM) := by
  let a := SixteenCoordinates.orientedLocalEquiv
  let c := NineCoordinates.canonicalLocalEquiv
  have hH₁ : (firstLocalModel ⊓ thirdLocalModel).subgroupOf firstLocalModel =
      SixteenCoordinates.localPairWords := by
    apply map_injective firstLocalModel.subtype_injective
    rw [map_subgroupOf_eq_of_le inf_le_left,NineCoordinates.first_third_intersection_eq_pair]
  have hH₃ : (firstLocalModel ⊓ thirdLocalModel).subgroupOf thirdLocalModel =
      NineCoordinates.thirdPairWords := by
    apply map_injective thirdLocalModel.subtype_injective
    rw [map_subgroupOf_eq_of_le inf_le_right,NineCoordinates.thirdPairWords_ambient]
  have h₁ : ((firstLocalModel ⊓ thirdLocalModel).subgroupOf firstLocalModel).map a.toMonoidHom =
      Seventeen.ModelAmalgam.pair := by
    rw [hH₁]
    exact SixteenCoordinates.orientedLocalEquiv_pairWords
  have h₃ : ((firstLocalModel ⊓ thirdLocalModel).subgroupOf thirdLocalModel).map c.toMonoidHom =
      CubicNormalizerModel.pair := by
    rw [hH₃]
    exact NineCoordinates.canonicalLocalEquiv_pair
  obtain ⟨f,b,δ,hf,hfp,hcompat⟩ :=
    Seventeen.ModelAmalgam.compatible_pair_maps_inner_field firstLocalModel thirdLocalModel
      CubicNormalizerModel.pair a c h₁ h₃ CubicNormalizerModel.modelPairEquiv
  have hp : SixteenCoordinates.localPointWords.map f.toMonoidHom = Seventeen.ModelAmalgam.point ∨
      SixteenCoordinates.localPointWords.map f.toMonoidHom = Seventeen.ModelAmalgam.oppositePoint := by
    have hh : SixteenCoordinates.localPointWords.map f.toMonoidHom =
        Seventeen.ModelAmalgam.point.map (MulAut.conj (b : M16)).toMonoidHom := by
      rw [hf]
      change SixteenCoordinates.localPointWords.map
        ((MulAut.conj (b : M16) * (if δ then Seventeen.ModelAmalgam.squareModel else 1)).toMonoidHom.comp
          a.toMonoidHom) = _
      rw [←map_map,SixteenCoordinates.orientedLocalEquiv_pointWords]
      cases δ
      · rfl
      · change Seventeen.ModelAmalgam.point.map ((MulAut.conj (b : M16)).toMonoidHom.comp
          Seventeen.ModelAmalgam.squareModel.toMonoidHom) = _
        rw [←map_map,Seventeen.ModelAmalgam.squareModel_point]
    rw [hh]
    exact Seventeen.ModelAmalgam.pair_conj_point_or_opposite b
  rcases hp with hp | hp
  · exact ⟨f,c,hp,hfp,h₃,NineCoordinates.canonicalLocalEquiv_third,
      NineCoordinates.canonicalLocalEquiv_kernel,hcompat⟩
  obtain ⟨b,_hb,_hbp,hbo,hbc⟩ :=
    Seventeen.ModelAmalgam.exists_pair_borel_inversion CubicNormalizerModel.modelPairEquiv
  let β := MulAut.conj (b : M16)
  let κ := CubicNormalizerModel.kernelInversion
  have hβ : Seventeen.ModelAmalgam.pair.map β.toMonoidHom = Seventeen.ModelAmalgam.pair :=
    mem_normalizer_iff_map_conj_eq.mp (Seventeen.ModelAmalgam.pair.le_normalizer b.property)
  refine ⟨f.trans β,c.trans κ,?_,?_,?_,?_,?_,?_⟩
  · change SixteenCoordinates.localPointWords.map (β.toMonoidHom.comp f.toMonoidHom) = _
    rw [←map_map,hp]
    exact hbo
  · change ((firstLocalModel ⊓ thirdLocalModel).subgroupOf firstLocalModel).map
      (β.toMonoidHom.comp f.toMonoidHom) = _
    rw [←map_map,hfp,hβ]
  · change ((firstLocalModel ⊓ thirdLocalModel).subgroupOf thirdLocalModel).map
      (κ.toMonoidHom.comp c.toMonoidHom) = _
    rw [←map_map,h₃]
    exact CubicNormalizerModel.kernelInversion_preimage CubicNormalizerModel.projectivePair
  · change NineCoordinates.thirdOverlapWords.map (κ.toMonoidHom.comp c.toMonoidHom) = _
    rw [←map_map,NineCoordinates.canonicalLocalEquiv_third]
    exact CubicNormalizerModel.kernelInversion_preimage CubicNormalizerModel.thirdFive
  · change NineCoordinates.cubicKernel.map (κ.toMonoidHom.comp c.toMonoidHom) = _
    rw [←map_map,NineCoordinates.canonicalLocalEquiv_kernel]
    exact CubicNormalizerModel.kernelInversion_preimage ⊥
  · intro x
    obtain ⟨z,hz₁,hz₃⟩ := hcompat x
    refine ⟨MulAut.conj b z,?_,?_⟩
    · change β (f ⟨x,x.property.1⟩) = _
      rw [hz₁]
      rfl
    · change κ (c ⟨x,x.property.2⟩) = _
      rw [hz₃]
      exact hbc z
end Sporadic.Janko3.AmalgamPresentation.ModelCoordinates
