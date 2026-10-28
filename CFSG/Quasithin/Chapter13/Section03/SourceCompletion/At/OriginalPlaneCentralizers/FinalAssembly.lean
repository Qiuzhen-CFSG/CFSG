module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.FinalAssembly
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.LinearThree.Frattini
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.ResidualAssembly

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalPlaneCentralizers.FinalAssembly`.
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

/-- Original 13.3.12(2), on the actual chosen module in every compatible full chart. -/
theorem planeCentralizers_of_source (s : Context T L V)
    :
    UnitaryPlaneCentralizers V (normalizer (L : Set G)) :=
  planeCentralizers_of_component_arguments s s.localExtraction s.componentInspection s.linearThreeExclusion

omit [IsElementaryAbelian 2 V] in
/-- The original strict-rank consumer with all plane-centralizer arguments discharged. -/
theorem unitary_rank_gt_three_of_original_plane_source
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (s : Context D.T D.L D.V)
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hHfull : D.H = normalizer (D.V₁ : Set G)) (hm : ⁅D.QH,B⁆ ≠ ⊥) :
    (3 : ℕ∞) < globalR D.V :=
  rank_gt_three_of_component_arguments D s s.localExtraction s.componentInspection s.linearThreeExclusion
    hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull hm

omit [IsElementaryAbelian 2 V] in
/-- The original unitary exclusion with the local plane-centralizer argument discharged. -/
theorem unitary_original_false_of_original_plane_source
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (s : Context D.T D.L D.V)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple D.T)
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hHfull : D.H = normalizer (D.V₁ : Set G)) (hm : ⁅D.QH,B⁆ ≠ ⊥)
    (hodd : UnitaryPrimeNormalizerControl D.L D.V) : False :=
  false_of_component_arguments D s s.localExtraction s.componentInspection s.linearThreeExclusion earlier
    hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull hm hodd

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
