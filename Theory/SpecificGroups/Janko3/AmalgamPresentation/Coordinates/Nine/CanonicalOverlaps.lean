module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.ModelOverlaps
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.RawCorrection

/-! The actual third local retains the simultaneous canonical correction of both full overlaps. -/
public noncomputable section
namespace Sporadic.Janko3.AmalgamPresentation.NineCoordinates
open Subgroup ModelCoordinates SourceRecognition.CubicNormalizerModel

/-- The actual third-local marking with both full canonical overlaps retained. -/
def canonicalLocalEquiv : thirdLocalModel ≃* Canonical :=
  thirdLocalEquiv.trans exists_raw_overlap_correction.choose

theorem canonicalLocalEquiv_pair :
    thirdPairWords.map canonicalLocalEquiv.toMonoidHom = pair := by
  change thirdPairWords.map
    (exists_raw_overlap_correction.choose.toMonoidHom.comp thirdLocalEquiv.toMonoidHom) = _
  rw [←map_map,thirdPairWords_map]
  exact exists_raw_overlap_correction.choose_spec.1

theorem canonicalLocalEquiv_third :
    thirdOverlapWords.map canonicalLocalEquiv.toMonoidHom = thirdOverlap := by
  change thirdOverlapWords.map
    (exists_raw_overlap_correction.choose.toMonoidHom.comp thirdLocalEquiv.toMonoidHom) = _
  rw [←map_map,thirdOverlapWords_map]
  exact exists_raw_overlap_correction.choose_spec.2.1

theorem canonicalLocalEquiv_kernel :
    cubicKernel.map canonicalLocalEquiv.toMonoidHom = projection.ker := by
  change cubicKernel.map
    (exists_raw_overlap_correction.choose.toMonoidHom.comp thirdLocalEquiv.toMonoidHom) = _
  rw [←map_map,cubicKernel_map]
  exact exists_raw_overlap_correction.choose_spec.2.2
end Sporadic.Janko3.AmalgamPresentation.NineCoordinates
