module

public import Stellmacher.SectionEight.EightSixCanonicalSmallIndex
public import Stellmacher.SectionEight.EightSixLargeIndexStructure
public import Stellmacher.SectionEight.GeneratedEightSixLargeIndexSetup
public import Stellmacher.SectionEight.GeneratedEightSixNoncontainmentSetup
public import Stellmacher.SectionEight.EightSixHighCostCaseC
public import Stellmacher.SectionEight.EightSixCostFourCaseB

/-!
# Stellmacher's three-case classification in (8.6)

The canonical theorem gives the common commutator and elementary-abelian
conclusions and the complete three alternatives declared in EightSixDefs.
It retains the original finite group, graph, prescribed predecessor and
subgroups D, L, Q, and Sylow three-subgroup T. In particular the fixed-point
and direct-product conclusions use that same supplied T.

The proved central first-step reduction supplies the initial SL2(2) quotient,
critical length two and initial center of order four. The common-structure
and small-index theorem settle index two. If the predecessor actor were
contained in D, equation one would force Q=D; its commutator bound would
collapse the initial core to its center, contradicting (8.3). The remaining
actor index is therefore at least four. The actual minimizing-actor selection
then splits by cost four or high cost. The complete case-B and case-C
producers provide all structural, numerical, fixed-action and normalizer
fields, and these join the common conclusions in the original public record.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.6), printed pp.41–45,
`refs/files/stellmacher-n-group.pdf`. The two case-C action fields retain the
approved quotient-fixed-coset and suitable-involution-lift definitions.
-/

open scoped BigOperators Pointwise

namespace Stellmacher.SectionEight

open Stellmacher.Later
open Stellmacher.SectionsFiveToSeven
open CosetGraphContext

universe u

/-- **Stellmacher (8.6).**  Under the hypothesis of (8.2), choose
`a−1 ∈ D(a)\{a+1}`, `D`, `L`, `Q`, and a Sylow 3-subgroup `T` as in the
paper.  Then the displayed commutator, elementary-abelian, and three-case
classification conclusions hold. -/
public theorem lemma_eight_six
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (aPrev : ctx.Γ.Vertex) (D L Q T : Subgroup H)
    (hprev : aPrev ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      aPrev ≠ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ aPrev ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ aPrev)
      (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (hT : IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a)) :
    LemmaEightSixConclusion ctx aPrev D L Q T := by
  classical
  by_cases hindex : QuotientCardEq (VAt ctx.Γ aPrev ⊓ QAt ctx.Γ ctx.criticalPath.a)
      ((VAt ctx.Γ aPrev ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2
  · exact lemma_eight_six_of_small_index ctx hcenter aPrev D L Q T hprev hD hL hQ hT hindex
  obtain ⟨data,hbase⟩ := eight_six_common_structure ctx hcenter aPrev hprev D L Q hD hL hQ
  obtain ⟨hquot,hlength⟩ := lemma_eight_five ctx hcenter
  obtain ⟨w,_⟩ := (lemma_eight_one ctx).barred_decomposition
  have hcard := eight_five_center_card_four_of_fixed_normal ctx hcenter w
    (lemma_eight_four ctx hcenter w)
  have hnot : ¬ VAt ctx.Γ aPrev ⊓ QAt ctx.Γ ctx.criticalPath.a ≤ D := by
    intro hcontained
    have hQD := eight_six_core_eq_intersection_of_previous_le
      ctx.toLocalContext.sectionSeven ctx.Γ ctx.criticalPath aPrev D L Q hprev.1 data hcontained
    have hbound := eight_six_initial_commutator_le_of_core_eq_intersection
      ctx.Γ ctx.criticalPath aPrev D L Q data hQ hQD hbase.1
    have heq := eight_three_core_eq_center ctx hcenter hbound
    apply lemma_eight_three ctx hcenter
    have hshort : ZAt ctx.Γ ctx.criticalPath.a ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
      apply SevenSix.critical_minimality ctx.Γ ctx.criticalPath
      rw [(SevenSix.adjacent_iff_distance_eq_one ctx.Γ).mp ctx.criticalPath.firstStep_adj]
      omega
    have hcore : twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) ≤ QAt ctx.Γ ctx.criticalPath.a := by
      change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a) ≤ ctx.Γ.twoCoreAt ctx.criticalPath.a
      rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,SevenSix.residual_core_eq_inter_core]
      exact inf_le_right
    exact hcore.trans (heq.le.trans hshort)
  have htwo : IsPGroup 2 (QAt ctx.Γ ctx.criticalPath.a) := by
    change IsPGroup 2 (ctx.Γ.twoCoreAt ctx.criticalPath.a)
    rw [ctx.Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p:=2)).map _
  have hlarge := (eight_six_index_ge_four_of_not_le
    (VAt ctx.Γ aPrev ⊓ QAt ctx.Γ ctx.criticalPath.a) D
    (htwo.to_le inf_le_right) hnot hindex).2
  obtain ⟨actor,E,A0,ha,hout,hmin,hedge,_,⟨geom⟩,hcore,_,_,hcost⟩ :=
    eight_six_large_index_structure_local ctx.toLocalContext hcenter hquot hlength hcard
      aPrev D L Q hprev hD hL hQ data hlarge
  refine ⟨hprev,⟨hD,hL,hQ,hT⟩,hbase,?_⟩
  rcases hcost with hfour | hhigh
  · exact eight_six_cost_four_case_b ctx hcenter hquot hlength hcard
      aPrev D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin
      hQ hfour T hT
  · exact eight_six_high_cost_case_c ctx hcenter hquot hlength hcard
      aPrev D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin
      hQ hhigh hbase.2.2 T hT

end Stellmacher.SectionEight
