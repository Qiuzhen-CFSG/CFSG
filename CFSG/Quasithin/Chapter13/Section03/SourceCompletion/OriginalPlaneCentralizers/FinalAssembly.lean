module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.LinearThree.Frattini
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.ResidualAssembly

/-!
# Original unitary plane-centralizer conclusion and consumers

The literal Q/V Frattini quotient gives the last L₃(2) contradiction.
Together with the original extraction, C.2.7 inspection and L₂(4)
perpendicular-space contradiction, this proves the plane-centralizer bound
in every compatible full chart. The strict-rank and original unitary
exclusion consumers use that bound on the same chosen module.

The genuine earlier Structural1222/catalogue inputs remain in Context;
Theorem12213 and odd-prime normalizer control remain with the final
13.3.16 assembly owner qt-d-13316-source. No local classification,
extraction, inspection or chief-factor callback remains.

Source: Aschbacher--Smith 13.3.12(2), pp.889--890, and 13.3.16--17,
pp.893--896.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
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
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
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

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
