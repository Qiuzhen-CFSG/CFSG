module
public import Stellmacher.SectionEleven.SylowTerminalContext
public import Stellmacher.SectionEight.LemmaEightTwo
public import Stellmacher.SectionEight.GeneratedEightFour
public import Stellmacher.SectionEight.GeneratedEightFiveCenterFour
public import Stellmacher.SectionEight.GeneratedEightFiveQuotientFromFour
public import Stellmacher.SectionEight.GeneratedEightFiveDistanceFromFour
public import Stellmacher.SectionEight.GeneratedEightSixNoncontainmentSetup
public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexOrders
public import Stellmacher.SectionEight.GeneratedEightSixLargeIndexSetup
public import Stellmacher.SectionEight.EightSixCommonStructure
public import Stellmacher.SectionEight.EightSixLargeIndexStructure
public import Stellmacher.SectionEight.EightSixCostFourSylowOrders
public import Stellmacher.SectionEight.EightSixHighCostSylowOrders

/-!
# The noncommuting critical-center Sylow bound

For the actual Sylow terminal context, noncommuting critical centers imply
that the original ambient Sylow subgroup has order at most 2^15. The global
Hypothesis Two remains on the ambient group; all local graph calculations
are performed on its generated join with the restricted original Sylow.

When the first-step center is noncentral, (8.2) makes the initial stabilizer
S4 or C2 times S4, so its subgroup S has order at most 48. Otherwise the
proved generated (8.4) and (8.5) give the initial order-four center, SL2(2)
quotient and critical length two. The actual predecessor and minimizing
actor split the calculation into small-index, cost-four and high-cost
cases. Their native numerical theorems bound S by 2^6, 2^10 and 2^15.
Finally the restriction equivalence transports the bound to the supplied
ambient Sylow, without any solvability assumption on all ambient two-locals.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.2), (8.6) and the
Theorem 1 application at the start of Section Eleven, printed pp.41–45,66.
-/

namespace Stellmacher.SectionEleven
open Later SectionsFiveToSeven CosetGraphContext SectionEight
universe u

private theorem generated_central_sylow_card_le
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    Nat.card (S.subgroupOf (P1 ⊔ P2)) ≤ 2 ^ 15 := by
  have hfirst := (SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr
    ctx.criticalPath.firstStep_adj
  have hZQ : ZAt ctx.Γ ctx.criticalPath.a ≤ QAt ctx.Γ ctx.criticalPath.a :=
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).center_core _ _ hfirst).trans
      (Subgroup.map_subtype_le _)
  have hQP : QAt ctx.Γ ctx.criticalPath.a ≤ GAt ctx.Γ ctx.criticalPath.a := by
    rw [show QAt ctx.Γ ctx.criticalPath.a =
      twoCoreIn (GAt ctx.Γ ctx.criticalPath.a) from ctx.Γ.twoCoreAt_def _]
    exact Subgroup.map_subtype_le _
  obtain ⟨w⟩ := exists_quotientModuleWitness
    (GAt ctx.Γ ctx.criticalPath.a) (ZAt ctx.Γ ctx.criticalPath.a)
    (hZQ.trans hQP) (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a)
  have hcard := generated_eight_five_center_card_four_of_fixed_normal
    ctx hcenter w (generated_lemma_eight_four ctx hcenter w)
  have hquot := generated_eight_five_quotient_of_card_four ctx hcenter hcard
  have hlength := generated_eight_five_length_of_card_four_and_quotient
    ctx hcenter hcard hquot
  obtain ⟨previous,D,L,Q,T,hprev,hD,hL,hQ,hT⟩ :=
    generated_eight_six_defining_witnesses ctx
  obtain ⟨data,hbase⟩ := eight_six_common_structure_local ctx.toLocalContext
    hcenter hquot hlength hcard previous hprev D L Q hD hL hQ
  by_cases hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2
  · have orders := eight_six_small_index_orders_local ctx.toLocalContext
      hcenter hquot hlength hcard previous D L Q T hprev
      ⟨hD,hL,hQ,hT⟩ hbase hindex data
    rcases orders.sylow_card ctx.sectionSeven ctx.Γ ctx.criticalPath hquot hcard
      with hsmall | hsmall <;> rw [hsmall] <;> norm_num
  have hnot := generated_eight_six_predecessor_intersection_not_le_of_equation_one
    ctx hcenter hlength previous D L Q hprev.1 data hQ hbase.1
  have hlarge := (generated_eight_six_index_ge_four_of_not_le ctx previous D hnot hindex).2
  obtain ⟨actor,E,A0,ha,hout,hmin,hedge,_,⟨geom⟩,hcore,_,_,hcost⟩ :=
    eight_six_large_index_structure_local ctx.toLocalContext hcenter hquot hlength hcard
      previous D L Q hprev hD hL hQ data hlarge
  rcases hcost with hfour | hhigh
  · exact (eight_six_cost_four_sylow_card_bounds ctx.toLocalContext hcenter hquot
      hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge
      hD hL ha hout hlarge hmin hQ hfour).2.trans (by norm_num)
  · exact (eight_six_high_cost_sylow_card_bounds ctx.toLocalContext hcenter hquot
      hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge
      hD hL ha hout hlarge hmin hQ hhigh hbase.2.2).2

public theorem noncommuting_terminal_sylow_card_le
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {P1 P2 : Subgroup H}
    (ctx : SylowTerminalContext H S0 P1 P2)
    (hcomm : ⁅ctx.Γ.z ctx.criticalPath.a, ctx.Γ.z ctx.criticalPath.a'⁆ ≠ ⊥) :
    Nat.card S0 ≤ 2 ^ 15 := by
  have hcard : Nat.card ((S0 : Subgroup H).subgroupOf (P1 ⊔ P2)) = Nat.card S0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe ctx.sylow_le_join).toEquiv
  rw [← hcard]
  by_cases hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)
  · exact generated_central_sylow_card_le (ctx.toSectionEightContext hcomm) hcenter
  have hbound := Subgroup.card_le_of_le
    (SevenSix.edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1
  have hmodels := lemma_eight_two_local
    (ctx.toSectionEightContext hcomm).toLocalContext hcenter ctx.criticalPath.a
  change IsModel (GAt ctx.Γ ctx.criticalPath.a) S4 ∨
    IsModel (GAt ctx.Γ ctx.criticalPath.a) (C2 × S4) at hmodels
  rcases hmodels with hmodel | hmodel
  · obtain ⟨e⟩ := hmodel
    rw [Nat.card_congr e.toEquiv] at hbound
    norm_num [S4, Nat.card_eq_fintype_card, Fintype.card_perm] at hbound
    exact hbound.trans (by norm_num)
  · obtain ⟨e⟩ := hmodel
    rw [Nat.card_congr e.toEquiv, Nat.card_prod] at hbound
    norm_num [C2, S4, Nat.card_eq_fintype_card, Fintype.card_perm] at hbound
    exact hbound.trans (by norm_num)

end Stellmacher.SectionEleven
