module
public import Stellmacher.SectionEleven.MultipleEightSixTerminal
public import Stellmacher.SectionEight.GeneratedEightFour
public import Stellmacher.SectionEight.GeneratedEightFiveCenterFour
public import Stellmacher.SectionEight.GeneratedEightFiveQuotientFromFour
public import Stellmacher.SectionEight.GeneratedEightFiveDistanceFromFour
public import Stellmacher.SectionEight.GeneratedEightSixCostFourReduction
public import Stellmacher.SectionEight.EightSixCostFourNormalizerWitness

/-!
# The central noncommuting terminal classification

For the actual Sylow terminal context, noncommuting critical centers and a
central first-step center give the Section Eight case-A type data or an
ambient nonsolvable two-local subgroup. All graph vertices and defining
subgroups remain in the original generated join.

The generated (8.4) fixed-normality theorem supplies (8.5): the initial
center has order four, the initial quotient is SL₂(2), and the critical
length is two. Choose the actual defining subgroups for (8.6). The generated
reduction already resolves case A and high cost. At cost four its native
normalizer witness gives an elementary subgroup of order sixteen with
nonsolvable normalizer, which embeds into the original ambient group.

Source: Stellmacher (8.6) and its Section Eleven application, printed
pp.41–45 and66–67. This adapter supplies the central noncommuting branch of
the final classification without a classification hypothesis.
-/
namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
private theorem generated_eight_five_full_consumer
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4 ∧
      QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
        (QAt ctx.Γ ctx.criticalPath.a) SL2Two ∧
      ctx.criticalPath.length = 2 := by
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
  have hfour := generated_eight_five_center_card_four_of_fixed_normal
    ctx hcenter w (generated_lemma_eight_four ctx hcenter w)
  have hquotient := generated_eight_five_quotient_of_card_four ctx hcenter hfour
  exact ⟨hfour, hquotient,
    generated_eight_five_length_of_card_four_and_quotient ctx hcenter hfour hquotient⟩

end Stellmacher.SectionEight

namespace Stellmacher.SectionEleven
open Later SectionsFiveToSeven CosetGraphContext SectionEight
universe u
public theorem multiple_eight_six_classification
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {P1 P2 : Subgroup H}
    (ctx : SylowTerminalContext H S0 P1 P2)
    (hcomm : ⁅ctx.Γ.z ctx.criticalPath.a, ctx.Γ.z ctx.criticalPath.a'⁆ ≠ ⊥)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    (∃ (previous : ctx.Γ.Vertex) (D L Q T : Subgroup (P1 ⊔ P2 : Subgroup H)),
      EightSixCaseATypeData ctx.Γ ctx.criticalPath previous D L Q T) ∨
      (∃ U : Subgroup H, IsTwoLocal U ∧ ¬ Group.IsSolvable U) := by
  let localCtx := ctx.toSectionEightContext hcomm
  obtain ⟨hcard,hquot,hlength⟩ := generated_eight_five_full_consumer localCtx hcenter
  obtain ⟨previous,D,L,Q,T,hprev,hD,hL,hQ,hT⟩ :=
    generated_eight_six_defining_witnesses localCtx
  rcases generated_eight_six_caseA_or_cost_four_or_bad_local localCtx hcenter
    hquot hlength hcard previous D L Q T hprev hD hL hQ hT with
      hA | ⟨E,A0,actor,⟨geom⟩,ha,hout,hmin,hedge,hcore,hlarge,hcost⟩ | hbad
  · exact Or.inl ⟨previous,D,L,Q,T,hA⟩
  · obtain ⟨data,_⟩ := eight_six_common_structure_local localCtx.toLocalContext
      hcenter hquot hlength hcard previous hprev D L Q hD hL hQ
    obtain ⟨W,_hWL,_hWnormal,helem,hWcard,hWbad⟩ := eight_six_cost_four_normalizer_witness
      localCtx.toLocalContext hcenter hquot hlength hcard previous D L Q hprev
      data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost
    exact Or.inr (ambient_bad_local_of_elementary_sixteen_normalizer
      (P1 ⊔ P2).subtype (P1 ⊔ P2).subtype_injective W helem hWcard hWbad)
  · exact Or.inr hbad

end Stellmacher.SectionEleven
