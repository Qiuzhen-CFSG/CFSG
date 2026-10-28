module
public import Stellmacher.MainType.EightSix
public import Stellmacher.SectionEight.GeneratedEightFour
public import Stellmacher.SectionEight.GeneratedEightFiveCenterFour
public import Stellmacher.SectionEight.GeneratedEightFiveQuotientFromFour
public import Stellmacher.SectionEight.GeneratedEightFiveDistanceFromFour
public import Stellmacher.SectionEight.GeneratedEightSixNoncontainmentSetup
public import Stellmacher.SectionEight.GeneratedEightSixLargeIndexSetup
public import Stellmacher.SectionEight.EightSixCommonStructure
public import Stellmacher.SectionEight.EightSixSmallIndexCaseA
public import Stellmacher.SectionEight.EightSixLargeIndexStructure
public import Stellmacher.SectionEight.EightSixCostFourCaseB
public import Stellmacher.SectionEight.EightSixHighCostCaseC

/-!
# All three source-local alternatives of generated (8.6)

The actual generated Section Eight graph with central first-step center has
one of the complete native configurations (8.6)(a), (b), or (c). The witnesses
are the actual predecessor and its defining subgroups D, L, Q and chosen
three-Sylow T. Every equation stays in the generated join, while global
Hypothesis Two stays on the original ambient group.

Generated (8.4) and (8.5) supply the order-four initial center, SL2(2)
quotient and critical length two. The defining witnesses and common-structure
theorem yield the common conclusions. Index two gives the proved small-index
case A. Otherwise noncontainment gives index at least four, so actual
minimal-actor selection splits into cost four and high cost. The same native
local producers used by the canonical B/C assemblies provide all numerical,
structural, prescribed-T, quotient-action and normalizer fields. This module
assembles those local fields directly and does not assume global hypotheses
for the join.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.4)–(8.6), printed
pp.40–45, and the local type definitions following (8.6).
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem generated_eight_six_type_classification
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    ∃ (previous : ctx.Γ.Vertex) (D L Q T : Subgroup (P1 ⊔ P2 : Subgroup H)),
      EightSixCaseATypeData ctx.Γ ctx.criticalPath previous D L Q T ∨
      EightSixCaseBTypeData ctx.Γ ctx.criticalPath previous D L Q T ∨
      EightSixCaseCTypeData ctx.Γ ctx.criticalPath previous D L Q T := by
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
  refine ⟨previous,D,L,Q,T,?_⟩
  obtain ⟨data,hbase⟩ := eight_six_common_structure_local ctx.toLocalContext
    hcenter hquot hlength hcard previous hprev D L Q hD hL hQ
  have hcommon : EightSixCommonTypeData ctx.Γ ctx.criticalPath previous D L Q T :=
    ⟨hprev,⟨hD,hL,hQ,hT⟩,hbase⟩
  by_cases hindex : QuotientCardEq (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2
  · exact Or.inl (eight_six_small_index_caseA_local ctx.toLocalContext hcenter
      hquot hlength hcard previous D L Q T hprev ⟨hD,hL,hQ,hT⟩ hbase hindex data)
  have hnot := generated_eight_six_predecessor_intersection_not_le_of_equation_one
    ctx hcenter hlength previous D L Q hprev.1 data hQ hbase.1
  have hlarge := (generated_eight_six_index_ge_four_of_not_le ctx previous D hnot hindex).2
  obtain ⟨actor,E,A0,ha,hout,hmin,hedge,_,⟨geom⟩,hcore,_,_,hcost⟩ :=
    eight_six_large_index_structure_local ctx.toLocalContext hcenter hquot hlength hcard
      previous D L Q hprev hD hL hQ data hlarge
  rcases hcost with hfour | hhigh
  · apply Or.inr ∘ Or.inl
    have hnormalizer := eight_six_cost_four_normalizer_witness ctx.toLocalContext
      hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom
      hcore hedge hD hL ha hout hlarge hmin hQ hfour
    have hsylow := eight_six_cost_four_sylow_card_bounds ctx.toLocalContext
      hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom
      hcore hedge hD hL ha hout hlarge hmin hQ hfour
    have hnext := eight_six_cost_four_next_quotient ctx.toLocalContext
      hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom
      hcore hedge hD hL ha hout hlarge hmin hQ hfour
    have hbound := eight_six_cost_four_initial_quotient_bound ctx.toLocalContext
      hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom
      hcore hedge hD hL ha hout hlarge hmin hQ hfour
    have hspecial := eight_six_cost_four_initial_residual_special ctx.toLocalContext
      hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom
      hcore hedge hD hL ha hout hlarge hmin hQ hfour
    have hpairEq := eight_six_cost_four_initial_pair_eq_residual_core ctx.toLocalContext
      hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom
      hcore hedge hD hL ha hout hlarge hmin hQ hfour
    have hquat := eight_six_cost_four_module_quaternion ctx.toLocalContext
      hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom
      hcore hedge hD hL ha hout hlarge hmin hQ hfour
    have hPhi := eight_six_next_core_frattini ctx.toLocalContext hcenter hlength hcard
      previous D L Q hprev.1 hD hL data hbase.2.2
    refine {
      toEightSixCommonTypeData := hcommon
      card_S := hsylow
      initial_quotient := hquot
      next_quotient := hnext
      initial_core := ?_
      next_core := ⟨hquat.1,hPhi⟩
      normalizer_witness := hnormalizer }
    refine ⟨hbound,hspecial.2,?_⟩
    change (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔
        (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a) =
          twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) at hpairEq
    rw [←hpairEq]
    exact ⟨(eight_six_cost_four_initial_pair_card ctx.toLocalContext hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hfour).2.2.2.2,
      eight_six_cost_four_initial_pair_fixed_free ctx.toLocalContext hcenter hquot hlength hcard
        previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hfour T hT⟩
  · apply Or.inr ∘ Or.inr
    have hsylow := eight_six_high_cost_sylow_card_bounds ctx.toLocalContext hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL
      ha hout hlarge hmin hQ hhigh hbase.2.2
    have hcubic := eight_six_high_cost_order_three_fixed_point_free ctx.toLocalContext hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL
      ha hout hlarge hmin hQ hhigh hbase.2.2
    have hres := eight_six_high_cost_residual_quotient_rank_four ctx.toLocalContext hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL
      ha hout hlarge hmin hQ hhigh hbase.2.2
    have horders := eight_six_high_cost_core_orders ctx.toLocalContext hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL
      ha hout hlarge hmin hQ hhigh hbase.2.2
    have hsplit := eight_six_high_cost_fixed_core_splitting ctx.toLocalContext hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL
      ha hout hlarge hmin hQ hhigh hbase.2.2 T hT
    have hextra := eight_six_high_cost_next_core_extraspecial ctx.toLocalContext hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL
      ha hout hlarge hmin hQ hhigh hbase.2.2
    have hcoreRank := eight_six_high_cost_core_action_rank ctx.toLocalContext hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL
      ha hout hlarge hmin hQ hhigh hbase.2.2
    have hinvol := eight_six_high_cost_quotient_involution_centralizes ctx.toLocalContext hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL
      ha hout hlarge hmin hQ hhigh hbase.2.2
    have hnormalizer := eight_six_high_cost_neighbor_normalizer ctx.toLocalContext
      hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge
      hD hL hhigh hQ
    have hnextcard : Nat.card (QAt ctx.Γ ctx.criticalPath.firstStep) = 512 := hextra.2
    refine {
      toEightSixCommonTypeData := hcommon
      card_S := hsylow
      initial_quotient := hquot
      next_residual := hres
      initial_core := ?_
      next_core := ?_
      quotient_three_action := hcubic
      quotient_involution_action := hinvol
      normalizer_quotient := hnormalizer }
    · exact ⟨by simpa only [show (2:ℕ)^6=64 from by decide] using horders.1,
        by simpa only [show (2:ℕ)^5=32 from by decide] using horders.2,hcard,hsplit⟩
    · exact ⟨hextra.1,by simpa only [show (2:ℕ)^9=512 from by decide] using hnextcard,hcoreRank⟩

end Stellmacher.SectionEight
