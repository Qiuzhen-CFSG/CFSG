module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.Residual
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.ExtractedAssembly

/-!
# Original consumers with component inspection discharged

The escaping original component has quotient SL₃(2), satisfies all binary
MS hypotheses on the literal join JQ, and equals O^{3′}(C_G(A)). Thus the
plane-centralizer conclusion and its two original unitary consumers retain
only the chief-factor contradiction from 13.3.12. That argument remains
with qt-d-13316-planes. The full earlier C.1.34 source theorem remains with
qt-rank-two-ms93, and final 13.3.16 assembly with qt-d-13316-source.

Source: Aschbacher--Smith 13.3.12, pp.889--890, and 13.3.16--17, pp.893--896.
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

/-- The original extraction and inspection are proved; only the chief-factor contradiction remains explicit. -/
theorem planeCentralizers_of_chief_factors (s : Context T L V)
    (hlinear : LinearThreeExclusion T L V) :
    UnitaryPlaneCentralizers V (normalizer (L : Set G)) :=
  planeCentralizers_of_component_arguments s s.localExtraction s.componentInspection hlinear

omit [IsElementaryAbelian 2 V] in
/-- Original consumer with extraction, inspection, MS input and residual identification discharged. -/
theorem rank_gt_three_of_chief_factors
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (s : Context D.T D.L D.V)
    (hlinear : LinearThreeExclusion D.T D.L D.V)
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hHfull : D.H = normalizer (D.V₁ : Set G)) (hm : ⁅D.QH,B⁆ ≠ ⊥) :
    (3 : ℕ∞) < globalR D.V :=
  rank_gt_three_of_component_arguments D s s.localExtraction s.componentInspection hlinear
    hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull hm

omit [IsElementaryAbelian 2 V] in
/-- Original consumer with extraction, inspection, MS input and residual identification discharged. -/
theorem false_of_chief_factors
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (s : Context D.T D.L D.V)
    (hlinear : LinearThreeExclusion D.T D.L D.V)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hHfull : D.H = normalizer (D.V₁ : Set G)) (hm : ⁅D.QH,B⁆ ≠ ⊥)
    (hodd : UnitaryPrimeNormalizerControl D.L D.V) : False :=
  false_of_component_arguments D s s.localExtraction s.componentInspection hlinear earlier
    hUV hZV hTZ hTU hZ hU B hBV hTB hB hHfull hm hodd

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
