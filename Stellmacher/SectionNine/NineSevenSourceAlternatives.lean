module

public import Stellmacher.SectionNine.NineSevenCommutatorCoreTransfer

/-!
# Excluding the actual source commutator alternatives

The cubic edge has prime index three. A terminal module escaping the initial
stabilizer therefore generates the first-step stabilizer with that edge.
The commutator alternatives give forbidden normality. A module staying in
the initial stabilizer instead lies in its core by the covariant-family
kernel, contradicting the nontrivial critical commutator. The initial and
first-step cubic quotient models and distance greater than four ensure the
edge generation and the two-group property of the source join. No terminal
core containment or normality conclusion is an input.

Source: Stellmacher (9.7), printed p.54 / PDF p.44, both normality alternatives
in the terminal-contained paragraph. `SourceInitialOddJoin` retains the
explicit two-step-walk definition from `NineSevenSourceOddW`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem cubic_edge_generate
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h7 : SectionSevenHypotheses G T A B) (Gamma : CosetGraphContext G T A B)
    {left right : Gamma.Vertex} (hadj : Gamma.adjacent left right)
    (hmodel : QuotientIsModel (GAt Gamma right) (QAt Gamma right) SL2Two)
    (actors : Subgroup G) (hactors : actors ≤ GAt Gamma right)
    (houtside : ¬ actors ≤ GAt Gamma left) :
    (GAt Gamma left ⊓ GAt Gamma right) ⊔ actors = GAt Gamma right := by
  let edge := GAt Gamma left ⊓ GAt Gamma right
  let joined := edge ⊔ actors
  have hQ : QAt Gamma right ≤ GAt Gamma right := by
    change Gamma.twoCoreAt right ≤ GAt Gamma right
    rw [Gamma.twoCoreAt_def]
    exact twoCoreIn_le _
  have hedge := (cubic_local_action_of_sl2Two_quotient Gamma h7 right hmodel).edge_card
    left (Gamma.adjacent_symm hadj)
  have hedgeCard : Nat.card edge = 2 * Nat.card (QAt Gamma right) := by
    change Nat.card (GAt Gamma right ⊓ GAt Gamma left : Subgroup G) = _ at hedge
    simpa only [edge, inf_comm] using hedge
  obtain ⟨projection, hsurj, hker⟩ := hmodel
  have hgroup := projection.ker.index_mul_card
  rw [Subgroup.index_ker, projection.range_eq_top_of_surjective hsurj,
    Subgroup.card_top, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ).toEquiv,
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card
      (show IsSL2Two SL2Two from ⟨MulEquiv.refl _⟩)] at hgroup
  have hindexProd := (edge.subgroupOf (GAt Gamma right)).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show edge ≤ GAt Gamma right from inf_le_right)).toEquiv, hedgeCard] at hindexProd
  have hindex : edge.relIndex (GAt Gamma right) = 3 := by
    change edge.relIndex (GAt Gamma right) * _ = _ at hindexProd
    have hpos := Nat.card_pos (α := QAt Gamma right)
    nlinarith
  have hjoined : joined ≤ GAt Gamma right := sup_le inf_le_right hactors
  have htower := Subgroup.relIndex_mul_relIndex edge joined (GAt Gamma right)
    le_sup_left hjoined
  rw [hindex] at htower
  have hdiv : edge.relIndex joined ∣ 3 := ⟨_, htower.symm⟩
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdiv with hone | hthree
  · exact (houtside ((le_sup_right.trans (Subgroup.relIndex_eq_one.mp hone)).trans
      inf_le_left)).elim
  · rw [hthree] at htower
    have hone : joined.relIndex (GAt Gamma right) = 1 := by omega
    exact le_antisymm hjoined (Subgroup.relIndex_eq_one.mp hone)

private theorem w_le_odd_w
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Gamma : CosetGraphContext G T A B) {vertex neighbor : Gamma.Vertex}
    (hadj : Gamma.adjacent vertex neighbor) :
    GeneratedNeighborhoodV Gamma vertex ≤ SourceOddW Gamma neighbor := by
  unfold GeneratedNeighborhoodV
  apply sSup_le
  rintro subgroup ⟨endpoint, hendpoint, rfl⟩
  exact le_sSup ⟨vertex,
    (mem_neighborhood_iff_adjacent Gamma).mpr (Gamma.adjacent_symm hadj),
    endpoint, hendpoint, rfl⟩

private theorem odd_w_normalized
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Gamma : CosetGraphContext G T A B) (vertex : Gamma.Vertex) :
    GAt Gamma vertex ≤ Subgroup.normalizer (SourceOddW Gamma vertex : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro actor hactor element helement
  have hfix : Gamma.act actor⁻¹ vertex = vertex :=
    (Set.ext_iff.mp (Gamma.stabilizer_def vertex) actor⁻¹).mp
      ((GAt Gamma vertex).inv_mem hactor)
  have hact := sourceOddW_act Gamma actor⁻¹ vertex
  simp only [inv_inv, hfix] at hact
  exact hact.symm ▸ Subgroup.mem_map_of_mem (MulAut.conj actor).toMonoidHom helement

public theorem nine_seven_source_commutator_alternatives_impossible
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 4 < ctx.criticalPath.length)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hfirstModel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (halternative :
      ⁅GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a, VAt ctx.Γ ctx.criticalPath.a'⁆ =
        ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ ∨
      ⁅SourceInitialOddJoin ctx.Γ ctx.criticalPath.a, VAt ctx.Γ ctx.criticalPath.a'⁆ =
        ⁅GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a, VAt ctx.Γ ctx.criticalPath.a'⁆) :
    False := by
  let Gamma := ctx.Γ
  let cp := ctx.criticalPath
  let W := GeneratedNeighborhoodV Gamma cp.a
  let U := SourceInitialOddJoin Gamma cp.a
  let terminal := VAt Gamma cp.a'
  let R := ⁅terminal, ZAt Gamma cp.a⁆
  have hbLocal : 4 < ctx.toLocalContext.criticalPath.length := hb
  have hWodd : W ≤ SourceOddW Gamma cp.firstStep := w_le_odd_w Gamma cp.firstStep_adj
  have hoddU : SourceOddW Gamma cp.firstStep ≤ U :=
    le_sSup ⟨cp.firstStep, (mem_neighborhood_iff_adjacent Gamma).mpr cp.firstStep_adj, rfl⟩
  have hfirstW : VAt Gamma cp.firstStep ≤ W :=
    nine_seven_neighbor_module_le_neighborhood Gamma cp.firstStep_adj
  have hZaW : ZAt Gamma cp.a ≤ W :=
    (lemma_seven_four ctx.sectionSeven Gamma cp).first_containment.1.trans hfirstW
  have hWne : W ≠ ⊥ := by
    intro hbot
    apply cp.critical.2
    change ZAt Gamma cp.a ≤ QAt Gamma cp.a'
    exact (hbot ▸ hZaW).trans bot_le
  have hUne : U ≠ ⊥ := by
    intro hbot
    exact hWne (le_bot_iff.mp (hbot ▸ hWodd.trans hoddU))
  have hUQ : U ≤ QAt Gamma cp.a := by
    unfold U SourceInitialOddJoin
    apply sSup_le
    rintro subgroup ⟨neighbor, hneighbor, rfl⟩
    have hdist : Gamma.distance neighbor cp.a ≤ 1 := Gamma.distance_le_of_path 1
      ![neighbor, cp.a] (by
        intro step
        fin_cases step
        exact Gamma.adjacent_symm ((mem_neighborhood_iff_adjacent Gamma).mp hneighbor))
    exact source_odd_w_le_core_of_distance Gamma cp neighbor cp.a (by dsimp [cp] at *; omega)
  have hUN : GAt Gamma cp.a ≤ Subgroup.normalizer (U : Set G) :=
    stabilizer_normalizes_source_initial_odd_join Gamma cp.a
  have hWN : GAt Gamma cp.a ≤ Subgroup.normalizer (W : Set G) :=
    nine_seven_stabilizer_normalizes_neighborhood Gamma cp.a
  have hterminalFirst : terminal ≤ GAt Gamma cp.firstStep :=
    (lemma_seven_four ctx.sectionSeven Gamma cp).reverse_containment.2
  have hcritical (hcore : terminal ≤ QAt Gamma cp.a) : False := by
    have hcentral : ZAt Gamma cp.a ≤ Subgroup.centralizer (QAt Gamma cp.a : Set G) :=
      ((lemma_seven_three ctx.sectionSeven Gamma).center_core cp.a cp.firstStep
        ((mem_neighborhood_iff_adjacent Gamma).mpr cp.firstStep_adj)).trans
        ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
    apply nine_seven_terminal_initial_commutator_ne_bot ctx
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hcentral.trans (Subgroup.centralizer_le hcore))
  by_cases hterminalInitial : terminal ≤ GAt Gamma cp.a
  · apply hcritical
    rcases halternative with hfirst | hsecond
    · apply nine_seven_neighborhood_commutator_forces_core ctx.toLocalContext (by omega)
        hmodel terminal hterminalInitial
      change ⁅W, terminal⁆ ≤ ZAt Gamma cp.a
      change ⁅W, terminal⁆ = R at hfirst
      rw [hfirst]
      exact (Subgroup.le_normalizer_iff_commutator_le_right.mp
        (hterminalInitial.trans (stabilizer_le_normalizer_z Gamma cp.a)))
    · apply nine_seven_source_join_commutator_forces_core ctx.toLocalContext (by omega)
        hmodel terminal hterminalInitial
      change ⁅U, terminal⁆ ≤ W
      change ⁅U, terminal⁆ = ⁅W, terminal⁆ at hsecond
      rw [hsecond]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hterminalInitial.trans hWN)
  · have hgenerate := cubic_edge_generate ctx.sectionSeven Gamma cp.firstStep_adj
      hfirstModel terminal hterminalFirst hterminalInitial
    rcases halternative with hfirst | hsecond
    · apply nine_seven_neighborhood_not_normalized_by_neighbor ctx.toLocalContext
        (by omega) cp.firstStep_adj hWne
      change GAt Gamma cp.firstStep ≤ Subgroup.normalizer (W : Set G)
      rw [← hgenerate]
      apply sup_le (inf_le_left.trans hWN)
      apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
      change ⁅W, terminal⁆ = R at hfirst
      rw [hfirst]
      exact ((nine_seven_terminal_initial_commutator_le_modules ctx).trans inf_le_left).trans hfirstW
    · apply hUne
      apply nine_seven_edge_invariant_two_subgroup_eq_bot ctx.sectionSeven Gamma cp.firstStep_adj U
        (nine_seven_subgroup_isTwoGroup_of_le_vertex_core Gamma cp.a U hUQ) hUN
      rw [← hgenerate]
      apply sup_le (inf_le_left.trans hUN)
      apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
      change ⁅U, terminal⁆ = ⁅W, terminal⁆ at hsecond
      rw [hsecond]
      exact ((Subgroup.commutator_mono hWodd le_rfl).trans
        (Subgroup.le_normalizer_iff_commutator_le_left.mp
          (hterminalFirst.trans (odd_w_normalized Gamma cp.firstStep)))).trans hoddU

end Stellmacher.SectionNine

