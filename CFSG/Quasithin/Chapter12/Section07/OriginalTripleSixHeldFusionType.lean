module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldAmbientExclusions
public import Theory.GroupTheory.Recognition.TransvectionFive.CoreFusionNormality
public import Theory.GroupTheory.Recognition.TransvectionFive.Uniqueness

/-! The original escaping configuration has both literal fusion counts
equal to forty-five once its actual whole centralizer is marked. The proved
linear and Mathieu uniqueness branches, together with original exclusions,
eliminate the other counts. This records source 40.5's local type boundary;
it does not assert the missing Held uniqueness theorem. -/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
open TransvectionFive TransvectionFive.UniquenessLinear
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Both actual rectangle fusion sets have forty-five elements, and both
actual root normalizers equal the prescribed point centralizer. -/
theorem original_tripleSix_escaping_fusion_type
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G))
    (z : G) (F : MarkedCentralizer z) (hcore : PointCoreFusion z) :
    (F.fusion F.plane).ncard = 45 ∧ (F.fusion F.threeSpace).ncard = 45 ∧
      F.HeldNormalizerPattern := by
  obtain ⟨_, _, hSL, _, hM⟩ :=
    original_tripleSix_escaping_ambient_exclusions h structural D a t ht heven hout
  have hsimple : IsSimpleGroup G := h.simpleQTKE.simple
  obtain ⟨hr, hc⟩ := CoreFusion.root_fusion F hsimple hcore
  have hp := FusionTypes.plane_count_of_tests F hr hc (CoreFusion.not_conjugate_core33 F)
  have ht' := FusionTypes.plane_count_of_tests (oppositeMarking F)
    ((CoreFusion.opposite_root_fusion F).1.mpr hc)
    ((CoreFusion.opposite_root_fusion F).2.mpr hr)
    (CoreFusion.not_conjugate_core33 (oppositeMarking F))
  have hs : (F.fusion F.threeSpace).ncard = 21 ∨ (F.fusion F.threeSpace).ncard = 45 := by
    simpa only [MarkedCentralizer.fusion, oppositeMarking_plane] using ht'
  obtain ⟨hl, hm⟩ := uniqueness_of_fusion hsimple z F hcore
  have h45 : (F.fusion F.plane).ncard = 45 ∧ (F.fusion F.threeSpace).ncard = 45 := by
    rcases hp with hp | hp <;> rcases hs with hs | hs
    · exact (hSL (hl ⟨hp, hs⟩)).elim
    · exact (hM (hm (Or.inl ⟨hp, hs⟩))).elim
    · exact (hM (hm (Or.inr ⟨hp, hs⟩))).elim
    · exact ⟨hp, hs⟩
  refine ⟨h45.1, h45.2, FusionTypes.row_normalizer_of_fortyfive F h45.1, ?_⟩
  have ho : ((oppositeMarking F).fusion (oppositeMarking F).plane).ncard = 45 := by
    simpa only [MarkedCentralizer.fusion, oppositeMarking_plane] using h45.2
  simpa only [oppositeMarking_row] using
    FusionTypes.row_normalizer_of_fortyfive (oppositeMarking F) ho

end CFSG.Quasithin.Chapter12.Section07
