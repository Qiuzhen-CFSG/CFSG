module

public import Theory.SpecificGroups.Held.SylowNormalSixteen
public import Theory.GroupTheory.Recognition.TransvectionFive.CoreFusionSingleRoot
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Row

/-! Native Held fusion counts from the literal Sylow-normal sixteen-subgroups.
A larger root normalizer would have relative index fifteen over the point
centralizer, contradicting its certified order prime to five. This excludes
both single-root fusion and the twenty-one-point rectangle alternative.
No ambient simplicity or abstract Held recognition premise is used. -/

public noncomputable section
open Subgroup Theory.GroupTheory.TransvectionFive
open Theory.GroupTheory.TransvectionFive.UniquenessLinear
namespace Held.TransvectionCentralizer

variable {z : He} (F : MarkedCentralizer z)

private theorem row_normalizer_not_five :
    ¬ 5 ∣ Nat.card (normalizer (F.row : Set He)) :=
  sylow_normal_sixteen_normalizer_not_five (sourceSylow F) F.row
    (flag_le_sourceSylow F).1 (source_row_elementary F) (row_card F)
    ((sourceSylow_le_point_centralizer F).trans (point_centralizer_le_row_normalizer F))

private theorem row_normalizer_eq :
    rowNormalizer F = centralizer ({z} : Set He) := by
  by_contra hne
  have hd := relIndex_dvd_card (centralizer ({z} : Set He)) (rowNormalizer F)
  rw [point_centralizer_row_index F hne] at hd
  exact row_normalizer_not_five F ((by decide : 5 ∣ 15).trans hd)

private theorem root_fusion (hcore : PointCoreFusion z) :
    IsConj z (PlaneTensor.element F 1) ∧ IsConj z (PlaneTensor.element F 32) := by
  have hd := CoreFusion.root_fusion_disjunction F hcore
  by_cases hr : IsConj z (PlaneTensor.element F 1)
  · refine ⟨hr, ?_⟩
    by_contra hc
    exact CoreFusion.row_only_normalizer_moves F hr hc (row_normalizer_eq F)
  · have hc := hd.resolve_left hr
    exact (CoreFusion.row_only_normalizer_moves (oppositeMarking F)
      ((CoreFusion.opposite_root_fusion F).1.mpr hc)
      (fun hh => hr ((CoreFusion.opposite_root_fusion F).2.mp hh))
      (row_normalizer_eq (oppositeMarking F))).elim

private theorem plane_fusion_count (hcore : PointCoreFusion z) :
    (F.fusion F.plane).ncard = 45 := by
  obtain ⟨hr, hc⟩ := root_fusion F hcore
  rcases FusionTypes.plane_count_of_tests F hr hc
    (CoreFusion.not_conjugate_core33 F) with h21 | h45
  · exact (UniquenessMathieu.SourceNormalizer.row_normalizer_ne F h21
      (row_normalizer_eq F)).elim
  · exact h45

/-- Both rectangle fusion sets in a marked native Held centralizer have
forty-five points whenever the actual point is not weakly closed in its core. -/
theorem fusion_counts (hcore : PointCoreFusion z) :
    (F.fusion F.plane).ncard = 45 ∧ (F.fusion F.threeSpace).ncard = 45 := by
  refine ⟨plane_fusion_count F hcore, ?_⟩
  simpa only [MarkedCentralizer.fusion, oppositeMarking_plane] using
    plane_fusion_count (oppositeMarking F) hcore

end Held.TransvectionCentralizer
