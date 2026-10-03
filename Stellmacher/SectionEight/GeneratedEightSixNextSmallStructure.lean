module

public import Stellmacher.SectionEight.GeneratedEightSixNextConjugateGeometry

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem eight_six_sylow_card_eq_twice_core
    {G : Type u} [Group G] [Finite G] (actors core : Subgroup G)
    (sylow : Sylow 2 actors) (hle : core ≤ actors)
    (hcore : core.subgroupOf actors ≤ sylow)
    (hquotient : QuotientIsModel actors core SL2Two) :
    Nat.card sylow = 2 * Nat.card core := by
  have hindex := eight_six_sylow_index_three_of_quotient
    actors core sylow hcore hquotient
  have hsylow := (sylow : Subgroup actors).index_mul_card
  rw [hindex] at hsylow
  obtain ⟨projection, hsurjective, hkernel⟩ := hquotient
  have hlocal := projection.ker.index_mul_card
  rw [Subgroup.index_ker, projection.range_eq_top_of_surjective hsurjective,
    Subgroup.card_top, hkernel,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hlocal
  have hmodel : Nat.card SL2Two = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩
  rw [hmodel] at hlocal
  omega

public theorem eight_six_next_core_card_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    {D Q : Subgroup G} (orders : EightSixSmallIndexOrderData graph path D Q)
    (hquot : QuotientIsModel (GAt graph path.a) (QAt graph path.a) SL2Two)
    (hcard : Nat.card (ZAt graph path.a) = 4)
    (hnext : QuotientIsModel (GAt graph path.firstStep)
      (QAt graph path.firstStep) SL2Two) :
    Nat.card (QAt graph path.firstStep) = 16 ∨
      Nat.card (QAt graph path.firstStep) = 32 := by
  obtain ⟨_, sylow, hsylow⟩ := (SevenSix.edge_sylow_data hyp graph path).2
  have hle : QAt graph path.firstStep ≤ GAt graph path.firstStep := by
    change graph.twoCoreAt path.firstStep ≤ graph.vertexStabilizer path.firstStep
    rw [graph.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hnative : (QAt graph path.firstStep).subgroupOf
      (GAt graph path.firstStep) ≤ sylow := by
    apply (Subgroup.map_le_map_iff_of_injective
      (GAt graph path.firstStep).subtype_injective).mp
    rw [Subgroup.map_subgroupOf_eq_of_le hle, hsylow]
    exact (SevenSix.local_cores_le_edge_sylow hyp graph path).2
  have hratio := eight_six_sylow_card_eq_twice_core _ _ sylow hle hnative hnext
  have hScard : Nat.card S = Nat.card sylow := by
    conv_lhs => rw [← hsylow]
    exact (Nat.card_congr ((sylow : Subgroup (GAt graph path.firstStep)).equivMapOfInjective
      (GAt graph path.firstStep).subtype
      (GAt graph path.firstStep).subtype_injective).toEquiv).symm
  have horders := orders.sylow_card hyp graph path hquot hcard
  rw [hScard] at horders
  rcases horders with hsmall | hlarge
  · left
    omega
  · right
    omega

public theorem eight_six_terminal_center_le_next_v
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    (hlength : path.length = 2) :
    ZAt graph path.a' ≤ VAt graph path.firstStep := by
  have hterminalNeighbor : path.a' ∈ neighborhood graph path.firstStep := by
    apply (SevenSix.mem_neighborhood_iff_adjacent graph).mpr
    have hstep := path.path_adj ⟨1, by omega⟩
    have hlast : (⟨1, by omega⟩ : Fin path.length).succ =
        ⟨path.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    rw [hlast, path.path_end] at hstep
    simpa only [Fin.castSucc_mk, path.path_first] using hstep
  rw [VAt, v, graph.vAt_def]
  exact le_sSup ⟨path.a', hterminalNeighbor, rfl⟩

public theorem eight_six_next_v_noncommutative_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hlength : ctx.criticalPath.length = 2) :
    ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
      VAt ctx.Γ ctx.criticalPath.firstStep⁆ ≠ ⊥ := by
  have hterminalV := eight_six_terminal_center_le_next_v ctx.Γ ctx.criticalPath hlength
  have hinitialV := (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.1
  intro hcomm
  apply ctx.commutator_ne
  apply le_bot_iff.mp
  exact (Subgroup.commutator_mono hinitialV hterminalV).trans hcomm.le

public theorem eight_six_next_v_derived_eq_line_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hcommutator : ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
      QAt ctx.Γ ctx.criticalPath.firstStep⁆ = ZAt ctx.Γ ctx.criticalPath.firstStep) :
    ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
      VAt ctx.Γ ctx.criticalPath.firstStep⁆ = ZAt ctx.Γ ctx.criticalPath.firstStep := by
  have hle : ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
      VAt ctx.Γ ctx.criticalPath.firstStep⁆ ≤ ZAt ctx.Γ ctx.criticalPath.firstStep := by
    rw [← hcommutator]
    exact Subgroup.commutator_mono le_rfl
      (SevenSix.neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath
        (by omega) ctx.criticalPath.firstStep)
  have hline := (eight_six_first_step_fixed_line_local ctx hcenter hcard).1
  have hne := eight_six_next_v_noncommutative_local ctx hlength
  have hpositive : 1 < Nat.card (⁅VAt ctx.Γ ctx.criticalPath.firstStep,
      VAt ctx.Γ ctx.criticalPath.firstStep⁆ : Subgroup G) := by
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  exact Subgroup.eq_of_le_of_card_ge hle (by omega)

public theorem eight_six_critical_centers_commutator_eq_line_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hcommutator : ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
      QAt ctx.Γ ctx.criticalPath.firstStep⁆ = ZAt ctx.Γ ctx.criticalPath.firstStep) :
    ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ ctx.criticalPath.a'⁆ =
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
  have hterminalV := eight_six_terminal_center_le_next_v ctx.Γ ctx.criticalPath hlength
  have hinitialV := (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.1
  have hderived := eight_six_next_v_derived_eq_line_local
    ctx hcenter hlength hcard hcommutator
  have hle := (Subgroup.commutator_mono hinitialV hterminalV).trans hderived.le
  have hline := (eight_six_first_step_fixed_line_local ctx hcenter hcard).1
  have hpositive : 1 < Nat.card (⁅ZAt ctx.Γ ctx.criticalPath.a,
      ZAt ctx.Γ ctx.criticalPath.a'⁆ : Subgroup G) :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr ctx.commutator_ne
  exact Subgroup.eq_of_le_of_card_ge hle (by omega)

end Stellmacher.SectionEight
