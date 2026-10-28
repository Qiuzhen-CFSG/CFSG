module
public import Stellmacher.SectionTen.TenOneCoreNeighborhoodNontrivial
public import Stellmacher.SectionTen.TenOneSmallNeighborhoodCard
public import Theory.GroupAction.FourTwoActionLine
public import Theory.GroupAction.SubgroupQuotientCommutatorImage

/-!
# The small residual-core neighborhood displacement line

In the small branch of Stellmacher (10.1), the first residual two-core has
a commutator image of order two on the generated middle neighborhood modulo
the first module. The hypotheses are the actual offset-two configuration,
the order-eight first module, and its local SL2(2) quotient.

The residual core lies in the first core and hence normalizes the middle
neighborhood and first module. Their literal quotient has order four, by
the proved neighborhood order thirty-two. The previous action-kernel
argument excludes trivial displacement. The finite four-element action
theorem then gives displacement order two, and the exact quotient
commutator-image theorem translates it to the stated relative index.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (10.1),
printed page 60, immediately following the common small-case indices.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_core_neighborhood_line
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    (VAt ctx.Γ ctx.criticalPath.firstStep).relIndex
      ⁅twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep),
        GeneratedNeighborhoodV ctx.Γ middle⁆ = 2 := by
  let R := twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)
  let U := GeneratedNeighborhoodV ctx.Γ middle
  let V := VAt ctx.Γ ctx.criticalPath.firstStep
  let P := GAt ctx.Γ ctx.criticalPath.firstStep
  obtain ⟨_, hfirst, _, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hb : 2 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hRQ : R ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.firstStep) ≤
      ctx.Γ.twoCoreAt ctx.criticalPath.firstStep
    rw [ctx.Γ.twoResidualAt_def, ctx.Γ.twoCoreAt_def, residual_core_eq_inter_core]
    exact inf_le_right
  have hRP : R ≤ P := hRQ.trans (by
    change ctx.Γ.twoCoreAt ctx.criticalPath.firstStep ≤ _
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _)
  have hRU : R ≤ Subgroup.normalizer (U : Set G) :=
    (hRQ.trans (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core
      ctx.criticalPath.firstStep middle
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hfirst))
      default).2.2)).trans (nine_seven_stabilizer_normalizes_neighborhood ctx.Γ middle)
  have hRV : R ≤ Subgroup.normalizer (V : Set G) :=
    hRP.trans (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep)
  have hUQ : U ≤ QAt ctx.Γ middle :=
    nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext hb middle
  have hUP : U ≤ P := hUQ.trans
    (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core middle
      ctx.criticalPath.firstStep ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) default).2.2)
  have hN : (V.subgroupOf U).Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    (hUP.trans (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep))
  let _ := hN
  have hVU : V ≤ U := le_sSup ⟨_, (mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst, rfl⟩
  have hquot : Nat.card (U ⧸ V.subgroupOf U) = 4 := by
    have hcount := Subgroup.card_eq_card_quotient_mul_card_subgroup (V.subgroupOf U)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVU).toEquiv] at hcount
    have hUcard : Nat.card U = 32 := ten_one_small_neighborhood_card ctx middle hpath hsmall
    change Nat.card V = 8 at hsmall
    rw [hsmall, hUcard] at hcount
    omega
  obtain ⟨action, haction⟩ := Subgroup.exists_quotient_conjugation_action R U V hRU hRV hN
  let actors := (R.subgroupOf R).map action
  have htwo : IsPGroup 2 actors := by
    have hRtwo : IsPGroup 2 R := (pCore_isPGroup (p := 2)
      (G := EAt ctx.Γ ctx.criticalPath.firstStep)).map _
    exact (hRtwo.to_subgroup (R.subgroupOf R)).map action
  have hcard := Subgroup.quotient_conjugation_commutatorAction_card
    R U V R hRU le_rfl hN action haction
  have hne : commutatorAction actors (U ⧸ V.subgroupOf U) ≠ ⊥ := by
    intro hbot
    have hone : V.relIndex ⁅U, R⁆ = 1 := by
      rw [← hcard]
      change Nat.card (commutatorAction actors (U ⧸ V.subgroupOf U)) = 1
      rw [hbot]
      simp
    apply ten_one_core_neighborhood_not_le_module ctx middle hpath hmodel
    rw [Subgroup.commutator_comm]
    exact Subgroup.relIndex_eq_one.mp hone
  have hline := commutatorAction_card_two_of_nontrivial_two_action_on_four htwo hquot hne
  rw [hcard] at hline
  rw [Subgroup.commutator_comm]
  exact hline
end Stellmacher.SectionTen
