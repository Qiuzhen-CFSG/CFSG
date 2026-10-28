module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Assembly
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.LocalControl
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Source

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalPlaneCentralizers.Assembly`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

/-- Exact plane-centralizer contract, conditional on the three unfinished source arguments. -/
theorem planeCentralizers_of_component_arguments (s : Context T L V)
    (hloc : LocalExtraction T L V) (hinspect : ComponentInspection T L V)
    (hlinear : LinearThreeExclusion T L V) :
    UnitaryPlaneCentralizers V (normalizer (L : Set G)) := by
  intro f E he hd A hAV hcard hn
  obtain ⟨f',E',he',_,hA,_⟩ := exists_plane_chart f E he hd A hAV hcard hn
  let d : MarkedPlane V := ⟨f',E',he',A,hAV,hA⟩
  by_contra hc
  obtain ⟨J,⟨j⟩⟩ := hloc d hc
  rcases hinspect d J j with hr | hl
  · obtain ⟨n,hnJ,hn⟩ := hr.cubic
    exact not_rankOne_of_source_join d.chart d.coordinates d.equivariant n hn
      J ((L ⊔ T).pCoreIn 2) hr.block hnJ j.input.normalizes hr.sylow
      hr.characteristic (chosen_perpendicular_central s d.coordinates)
  · obtain ⟨hl⟩ := hl
    exact hlinear d J j hl

omit [IsElementaryAbelian 2 V] in
/-- Application to the original strict-rank consumer, on the same chosen module. -/
theorem rank_gt_three_of_component_arguments
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (s : Context D.T D.L D.V)
    (hloc : LocalExtraction D.T D.L D.V)
    (hinspect : ComponentInspection D.T D.L D.V)
    (hlinear : LinearThreeExclusion D.T D.L D.V)
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hHfull : D.H = normalizer (D.V₁ : Set G)) (hm : ⁅D.QH,B⁆ ≠ ⊥) :
    (3 : ℕ∞) < globalR D.V := by
  have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
  obtain ⟨hTV,hNL⟩ := unitary_original_module_normalizers s.hypothesis s.maximal
    s.quotient s.chosen s.structural
  let : IsSimpleGroup Atlas.G2.Natural.BinaryNormalizer.Derived :=
    Atlas.G2.isSimple_commutator_binary
  have hs := s.quotient.isSimpleGroup
  have hfaith : D.L ⊓ centralizer (D.V : Set G) ≤ D.L.pCoreIn 2 := by
    have hc := congrArg (map D.L.subtype) (s.chosen.centralizer_eq_core_of_simple hs)
    exact (show D.L ⊓ centralizer (D.V : Set G) = D.L.pCoreIn 2 by
      simpa only [pCoreIn,subgroupOf_map_subtype,inf_comm] using hc).le
  have huniq := h12.source_normalizer_maximal_unique_at s.structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  exact unitary_rank_gt_three_of_earlier_geometry D s.actor s.coordinates s.equivariant
    hUV hZV hTZ hTU hZ hU
    ((pResidual_eq_top_iff 2 D.L).mpr
      (Chapter1.Section02.Adequate.mem_L_isPPerfect s.maximal.1))
    s.chosen.sylow_normalizes_component (s.chosen.le_sylow.trans le_sup_right)
    ((s.structural D.L h12).2.2 D.V s.chosen).2.1
    (unitary_chosen_sylow_kernel s.chosen hs hTV) hNL hfaith huniq.2
    B hBV hTB hB hHfull hm s.hypothesis.qtke
    (h12.source_chosen_TI_at s.structural s.chosen)
    (planeCentralizers_of_component_arguments s hloc hinspect hlinear)
    (maximalEscapeAction_of_source s.earlier_geometry.1)

omit [IsElementaryAbelian 2 V] in
/-- Application to original 13.3.16, retaining its independent earlier-source inputs. -/
theorem false_of_component_arguments
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (s : Context D.T D.L D.V)
    (hloc : LocalExtraction D.T D.L D.V)
    (hinspect : ComponentInspection D.T D.L D.V)
    (hlinear : LinearThreeExclusion D.T D.L D.V)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple D.T)
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hHfull : D.H = normalizer (D.V₁ : Set G)) (hm : ⁅D.QH,B⁆ ≠ ⊥)
    (hodd : UnitaryPrimeNormalizerControl D.L D.V) : False := by
  exact unitary_original_false_of_earlier_sources D s.hypothesis s.maximal s.quotient
    s.chosen s.structural earlier s.actor s.coordinates s.equivariant
    hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull hm
    (planeCentralizers_of_component_arguments s hloc hinspect hlinear)
    (maximalEscapeAction_of_source s.earlier_geometry.1) hodd

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
