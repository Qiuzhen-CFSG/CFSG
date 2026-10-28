module
public import Theory.GroupTheory.Recognition.TransvectionFive.CoreFusionRoots
public import Theory.GroupTheory.Recognition.TransvectionFive.CoreFusionCensus
public import Theory.GroupTheory.Recognition.TransvectionFive.FusionTypes
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Plane
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceFullAction

/-!
# The one-root fusion alternative on the original rectangles

Transport the finite single-root census through the same marked matrix
coordinates. When only the row orbit fuses, the two literal rectangle
fusion sets consist precisely of their row points and have orders seven
and three. The full plane normalizer preserves the row-plane intersection,
hence normalizes the original row. Its fusion element moves the marked
point, giving the full row-normalizer action by the already proved 39.3.

These are the local one-root reductions in Aschbacher, *Sporadic Groups*
(1994), 39.7–39.8, pp.214–216. They do not yet prove the global normality
conclusion of 39.9. That conclusion and the final dimension-four assembly
remain with `qt-d-12213-four-recognition`.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.CoreFusion
open UniquenessLinear PlaneTensor
open UniquenessMathieu.SourceNormalizer
variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

/-- Reversing the flag exchanges the two actual root-fusion assertions. -/
theorem opposite_root_fusion :
    (IsConj z (element (oppositeMarking F) 1) ↔ IsConj z (element F 32)) ∧
    (IsConj z (element (oppositeMarking F) 32) ↔ IsConj z (element F 1)) := by
  constructor
  · rw [row_fusion_iff,column_fusion_iff,oppositeMarking_row]
  · rw [column_fusion_iff,row_fusion_iff,oppositeMarking_column]

variable [Finite G]
omit [Finite G] in
private theorem fusionCodes_nonzero : (0 : PlaneCensus.Code) ∉ fusionCodes F := by
  intro h
  have hh := (mem_fusionCodes F 0).mp h
  rw [element_zero,isConj_one_left] at hh
  have ho := F.point_orderOf
  simp [hh] at ho

omit [Finite G] in
private theorem fusionCodes_shear (k : Fin 5) (a : PlaneCensus.Code) :
    PlaneCensus.shear k a ∈ fusionCodes F ↔ a ∈ fusionCodes F := by
  rw [mem_fusionCodes,mem_fusionCodes]
  obtain ⟨n,_,hn⟩ := exists_shear_conjugator F k a
  exact (conjugate_fusion (z := z) (isConj_iff.mpr ⟨n,hn⟩)).symm

/-- With the column orbit absent, the row orbit accounts for every fused
point of the original plane. -/
theorem row_only_plane_codes (hrow : IsConj z (element F 1))
    (hcolumn : ¬ IsConj z (element F 32)) (x : PlaneCensus.Code) :
    IsConj z (element F x) ↔ x ≠ 0 ∧ x >>> 3 = 0 := by
  rw [← mem_fusionCodes]
  apply CoreFusionCensus.row_only (fusionCodes F) (fusionCodes_nonzero F)
    ((mem_fusionCodes F 1).mpr hrow) ?_
    (fun h => hcolumn ((mem_fusionCodes F 32).mp h))
    (fun h => not_conjugate_core33 F ((mem_fusionCodes F 33).mp h))
    (fusionCodes_shear F) (fusionCodes_pairCount F) x
  rw [mem_fusionCodes,element_point]

/-- The opposite asymmetric case has only the three nonzero column points. -/
theorem column_only_plane_codes (hrow : ¬ IsConj z (element F 1))
    (hcolumn : IsConj z (element F 32)) (x : PlaneCensus.Code) :
    IsConj z (element F x) ↔ x = 4 ∨ x = 32 ∨ x = 36 := by
  rw [← mem_fusionCodes]
  apply CoreFusionCensus.column_only (fusionCodes F) (fusionCodes_nonzero F)
    (fun h => hrow ((mem_fusionCodes F 1).mp h)) ?_
    ((mem_fusionCodes F 32).mpr hcolumn)
    (fun h => not_conjugate_core33 F ((mem_fusionCodes F 33).mp h))
    (fusionCodes_shear F) (fusionCodes_pairCount F) x
  rw [mem_fusionCodes,element_point]

/-- Source 39.7's exact seven-point count. -/
theorem row_only_plane_count (hrow : IsConj z (element F 1))
    (hcolumn : ¬ IsConj z (element F 32)) : (F.fusion F.plane).ncard = 7 := by
  classical
  rw [← fusionCodes_card F rfl]
  have he : fusionCodes F = Finset.univ.filter (fun x : PlaneCensus.Code => x ≠ 0 ∧ x >>> 3 = 0) := by
    ext x
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,mem_fusionCodes] using
      row_only_plane_codes F hrow hcolumn x
  rw [he]
  decide

theorem column_only_plane_count (hrow : ¬ IsConj z (element F 1))
    (hcolumn : IsConj z (element F 32)) : (F.fusion F.plane).ncard = 3 := by
  classical
  rw [← fusionCodes_card F rfl]
  have he : fusionCodes F = ({4,32,36} : Finset PlaneCensus.Code) := by
    ext x
    simpa only [Finset.mem_insert,Finset.mem_singleton,mem_fusionCodes] using
      column_only_plane_codes F hrow hcolumn x
  rw [he]
  decide

/-- In the one-root branch both actual rectangle fusion sets are measured. -/
theorem row_only_counts (hrow : IsConj z (element F 1))
    (hcolumn : ¬ IsConj z (element F 32)) :
    (F.fusion F.plane).ncard = 7 ∧ (F.fusion F.threeSpace).ncard = 3 := by
  refine ⟨row_only_plane_count F hrow hcolumn,?_⟩
  have hh := column_only_plane_count (oppositeMarking F)
    (fun h => hcolumn ((opposite_root_fusion F).1.mp h))
    ((opposite_root_fusion F).2.mpr hrow)
  simpa only [MarkedCentralizer.fusion,oppositeMarking_plane] using hh

/-- Every fused plane element belongs to the original row, not just to
an abstract seven-point set. -/
theorem row_only_plane_fusion_mem (hrow : IsConj z (element F 1))
    (hcolumn : ¬ IsConj z (element F 32)) {a : G}
    (ha : a ∈ F.plane) (hf : IsConj z a) : a ∈ F.row := by
  obtain ⟨x,hx⟩ := (sourceEquiv F).surjective ⟨a,ha⟩
  have he : element F x = a := congrArg Subtype.val hx
  rw [← he,element_mem_row_iff]
  have hc := ((row_only_plane_codes F hrow hcolumn x).mp (he.symm ▸ hf)).2
  simpa only [rowCodes,Finset.mem_filter,Finset.mem_univ,true_and] using hc

private theorem column_only_plane_fusion_mem (hrow : ¬ IsConj z (element F 1))
    (hcolumn : IsConj z (element F 32)) {a : G}
    (ha : a ∈ F.plane) (hf : IsConj z a) : a ∈ F.column := by
  obtain ⟨x,hx⟩ := (sourceEquiv F).surjective ⟨a,ha⟩
  have he : element F x = a := congrArg Subtype.val hx
  rw [← he]
  rcases (column_only_plane_codes F hrow hcolumn x).mp (he.symm ▸ hf) with rfl | rfl | rfl
  · rw [element_point]; exact point_mem_column F
  · exact element32_mem_column F
  · have hxor : (4 : PlaneCensus.Code) ^^^ 32 = 36 := by decide
    rw [← hxor,element_xor,element_point]
    exact F.column.mul_mem (point_mem_column F) (element32_mem_column F)

/-- The three-space rectangle also has no fused points outside the original row. -/
theorem row_only_threeSpace_fusion_mem (hrow : IsConj z (element F 1))
    (hcolumn : ¬ IsConj z (element F 32)) {a : G}
    (ha : a ∈ F.threeSpace) (hf : IsConj z a) : a ∈ F.row := by
  have hh := column_only_plane_fusion_mem (oppositeMarking F)
    (fun h => hcolumn ((opposite_root_fusion F).1.mp h))
    ((opposite_root_fusion F).2.mpr hrow) (a := a)
    (by simpa only [oppositeMarking_plane] using ha) hf
  simpa only [oppositeMarking_column] using hh

/-- Source 39.7: the full plane normalizer preserves the actual root group. -/
theorem row_only_plane_normalizer_le (hrow : IsConj z (element F 1))
    (hcolumn : ¬ IsConj z (element F 32)) :
    normalizer (F.plane : Set G) ≤ rowNormalizer F := by
  intro g hg
  have hn : g ∈ normalizer ((F.row ⊓ F.plane : Subgroup G) : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨a,ha,rfl⟩
      have hA := (mem_normalizer_iff.mp hg a).mp ha.2
      refine ⟨?_,hA⟩
      by_cases he : a = 1
      · simp [he]
      · exact row_only_plane_fusion_mem F hrow hcolumn hA
          (((row_fusion_iff F).mp hrow a ha.1 he).trans (isConj_iff.mpr ⟨g,rfl⟩))
    · rw [card_map_of_injective (MulAut.conj g).injective]
  rw [source_row_plane_normalizer] at hn
  exact hn.1

/-- The one-root branch has the full four-dimensional row-normalizer action,
as in 39.7(1); its point centralizer is a proper subgroup. -/
theorem row_only_normalizer_moves (hrow : IsConj z (element F 1))
    (hcolumn : ¬ IsConj z (element F 32)) :
    rowNormalizer F ≠ Subgroup.centralizer ({z} : Set G) := by
  obtain ⟨n,hn,he⟩ := source_plane_fusion F (point_mem_plane F) (element_mem F 1) hrow
  intro heq
  have hc : n ∈ Subgroup.centralizer ({z} : Set G) :=
    heq ▸ row_only_plane_normalizer_le F hrow hcolumn hn
  exact element_one_ne_point F (he.symm.trans
    (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hc)))

end Theory.GroupTheory.TransvectionFive.CoreFusion
