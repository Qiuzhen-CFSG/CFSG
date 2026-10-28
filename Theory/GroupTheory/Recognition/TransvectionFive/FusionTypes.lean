module

public import Theory.GroupTheory.Recognition.TransvectionFive.FusionTypesCensus
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Plane
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Column
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRowFlags
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Plane
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Column
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceFusion

/-!
# Fusion alternatives after the source core-fusion calculation

Ambient normalizer fusion gives constant additive pair counts on each
rectangle's fusion set. The finite orbit census then gives counts 21 or 45
from three actual core representatives. Independently, full row-normalizer
action forces seven to divide the corresponding rectangle count. Hence
45 forces that root normalizer to equal the full point centralizer; if
both counts are 45, both literal normalizer equalities hold.

The internal imports reuse the already proved fusion-coordinate transport,
relative-index identity and row-intersection orbit calculation. No public
boundary of the uniqueness producers is changed. The source 39.10 core
fusion facts are explicit inputs, retained by the final assembly owner
`qt-d-12213-four-recognition`; this module does not prove them from simplicity.
Source: Aschbacher, *Sporadic Groups* (1994), 39.3, 39.6, 39.10 and 40.2–40.5,
pp.214–219.
-/

public noncomputable section


open Subgroup
namespace Theory.GroupTheory.TransvectionFive.FusionTypes
open UniquenessLinear UniquenessLinear.PlaneTensor
open UniquenessMathieu.SourceNormalizer
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

theorem plane_count_of_tests
    (h1 : IsConj z (element F 1)) (h32 : IsConj z (element F 32))
    (h33 : ¬ IsConj z (element F 33)) :
    (F.fusion F.plane).ncard = 21 ∨ (F.fusion F.plane).ncard = 45 := by
  classical
  have hc : (fusionCodes F).card = (F.fusion F.plane).ncard := fusionCodes_card F rfl
  rw [← hc]
  apply FusionTypesCensus.card_dichotomy (fusionCodes F) ?_
    ((mem_fusionCodes F 1).mpr h1) ?_ ((mem_fusionCodes F 32).mpr h32)
    (fun h => h33 ((mem_fusionCodes F 33).mp h)) ?_
    (fusionCodes_pairCount F 1 ((mem_fusionCodes F 1).mpr h1))
  · intro h
    have he := (mem_fusionCodes F 0).mp h
    rw [element_zero, isConj_one_left] at he
    have ho := F.point_orderOf
    simp [he] at ho
  · rw [mem_fusionCodes,element_point]
  · intro k a
    rw [mem_fusionCodes,mem_fusionCodes]
    obtain ⟨n,_,hn⟩ := exists_shear_conjugator F k a
    exact (conjugate_fusion (z := z) (isConj_iff.mpr ⟨n,hn⟩)).symm

theorem seven_dvd_plane_fusion_of_row_moves
    (hne : rowNormalizer F ≠ centralizer ({z} : Set G)) :
    7 ∣ (F.fusion F.plane).ncard := by
  let H := centralizer ({z} : Set G)
  let M := normalizer (F.plane : Set G)
  let K := rowNormalizer F ⊓ normalizer ((F.row ⊓ F.plane : Subgroup G) : Set G)
  have hKM : K ≤ M := inf_le_right.trans (source_row_plane_normalizer_le_plane F)
  have hHK : H ⊓ M ≤ K := by
    intro h hh
    have hr := point_centralizer_le_row_normalizer F hh.1
    exact ⟨hr, inf_normalizer_le_normalizer_inf ⟨hr, hh.2⟩⟩
  have ht := relIndex_mul_relIndex (H ⊓ M) K M hHK hKM
  have he : (H ⊓ M).relIndex K = H.relIndex K := by
    rw [relIndex,relIndex]
    congr 1
    ext k
    exact and_iff_left (hKM k.property)
  rw [he,inf_relIndex_right,row_intersection_orbit F hne] at ht
  have hi : H.relIndex M = (F.fusion F.plane).ncard :=
    normalizer_point_index F F.plane (point_mem_plane F)
      (fun _ ha hf => source_plane_fusion F (point_mem_plane F) ha hf)
  exact ⟨K.relIndex M, by rw [← hi]; exact ht.symm⟩

theorem row_normalizer_of_fortyfive (h45 : (F.fusion F.plane).ncard = 45) :
    normalizer (F.row : Set G) = centralizer ({z} : Set G) := by
  by_contra hne
  have hd := seven_dvd_plane_fusion_of_row_moves F hne
  rw [h45] at hd
  norm_num at hd

theorem alternatives_of_counts
    (hplane : (F.fusion F.plane).ncard = 21 ∨ (F.fusion F.plane).ncard = 45)
    (hthree : (F.fusion F.threeSpace).ncard = 21 ∨ (F.fusion F.threeSpace).ncard = 45) :
    F.LinearFusion ∨ F.MathieuFusion ∨ F.HeldNormalizerPattern := by
  rcases hplane with hp | hp <;> rcases hthree with ht | ht
  · exact Or.inl ⟨hp,ht⟩
  · exact Or.inr (Or.inl (Or.inl ⟨hp,ht⟩))
  · exact Or.inr (Or.inl (Or.inr ⟨hp,ht⟩))
  · refine Or.inr (Or.inr ⟨row_normalizer_of_fortyfive F hp, ?_⟩)
    have ho : ((oppositeMarking F).fusion (oppositeMarking F).plane).ncard = 45 := by
      simpa only [MarkedCentralizer.fusion,oppositeMarking_plane] using ht
    simpa only [oppositeMarking_row] using row_normalizer_of_fortyfive (oppositeMarking F) ho

theorem alternatives_of_tests
    (h1 : IsConj z (element F 1)) (h32 : IsConj z (element F 32))
    (h33 : ¬ IsConj z (element F 33))
    (h1' : IsConj z (element (oppositeMarking F) 1))
    (h32' : IsConj z (element (oppositeMarking F) 32))
    (h33' : ¬ IsConj z (element (oppositeMarking F) 33)) :
    F.LinearFusion ∨ F.MathieuFusion ∨ F.HeldNormalizerPattern := by
  apply alternatives_of_counts F (plane_count_of_tests F h1 h32 h33)
  simpa only [MarkedCentralizer.fusion,oppositeMarking_plane] using
    plane_count_of_tests (oppositeMarking F) h1' h32' h33'

end Theory.GroupTheory.TransvectionFive.FusionTypes
