module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import Theory.GroupTheory.SylowImageIntersection
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.QuotientIntersection
public import Theory.GroupTheory.CComponent.Basic
/-!
# Literal overlap and Sylow coordinates in the source star quotient

The maximal subgroup contains the quotient kernel, so its component
intersection maps to the intersection of the images. A prescribed Sylow
intersection with a subnormal component is itself Sylow there; its image
therefore remains the precise Sylow intersection after quotienting.
These identities identify the source centralizer clause with the ordinary
internal centralizer formula used by the concrete model producers.

Source: Aschbacher–Smith E.2.2, printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
/-- The literal maximal overlap is the maximal image restricted to the same component image. -/
theorem source_overlap_coordinate (M K : Subgroup H) :
    componentOverlap M K = (sourceImage M M).subgroupOf (sourceImage M K) := by
  have he : sourceImage M (M ⊓ K) = sourceImage M M ⊓ sourceImage M K := by
    change (M ⊓ K).map (QuotientGroup.mk' M.normalCore) =
      M.map (QuotientGroup.mk' M.normalCore) ⊓ K.map (QuotientGroup.mk' M.normalCore)
    rw [inf_comm M K,map_inf_of_ker_le _ K M (by rw [QuotientGroup.ker_mk'];exact M.normalCore_le),inf_comm]
  rw [componentOverlap,he,inf_subgroupOf_right]

/-- The original component Sylow intersection is unchanged by its literal quotient image. -/
theorem source_sylow_coordinate (M K : Subgroup H) (T : Sylow 2 H)
    (hK : K.IsSubnormal) :
    (sourceImage M ((T : Subgroup H) ⊓ K)).subgroupOf (sourceImage M K) =
      (sourceImage M (T : Subgroup H)).subgroupOf (sourceImage M K) := by
  obtain ⟨P,hP⟩ := T.exists_subgroupOf_eq_of_subnormal K hK
  have hi := T.map_image_eq_inf K ((T : Subgroup H) ⊓ K) P
    (by rw [hP,subgroupOf_map_subtype]) inf_le_left (QuotientGroup.mk' (sourceKernel M))
  change (((T : Subgroup H) ⊓ K).map (QuotientGroup.mk' (sourceKernel M))).subgroupOf _ = _
  change (((T : Subgroup H) ⊓ K).map (QuotientGroup.mk' (sourceKernel M))).subgroupOf
    (K.map (QuotientGroup.mk' (sourceKernel M))) =
    ((T : Subgroup H).map (QuotientGroup.mk' (sourceKernel M))).subgroupOf
    (K.map (QuotientGroup.mk' (sourceKernel M)))
  rw [hi,inf_subgroupOf_right]

/-- The high source centralizer clause is the exact internal quotient centralizer identity. -/
theorem centralizerOverlap_iff_star (M K : Subgroup H) (T : Sylow 2 H)
    (hK : K.IsSubnormal) :
    CentralizerOverlap M K (T : Subgroup H) ↔
      (sourceImage M M).subgroupOf (sourceImage M K) = centralizer
        ((center ((sourceImage M (T : Subgroup H)).subgroupOf (sourceImage M K))).map
          ((sourceImage M (T : Subgroup H)).subgroupOf (sourceImage M K)).subtype : Set _) := by
  unfold CentralizerOverlap
  rw [source_overlap_coordinate,source_sylow_coordinate M K T hK]
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
