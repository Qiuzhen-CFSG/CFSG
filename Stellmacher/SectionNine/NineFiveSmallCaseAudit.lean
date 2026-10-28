module

public import Stellmacher.SectionNine.NineFivePenultimateCoreNontrivialReduction
public import Stellmacher.SectionNine.NineThreeInitialExtractionInputs
public import Stellmacher.SectionNine.NineNextVModule
public import Stellmacher.SectionNine.NineSevenCommutatorActionBridge

/-!
# The order-eight obstruction to penultimate residual exclusion

In an order-eight terminal module, the four-element penultimate center has
index two. An actor from the first-step module normalizes both groups, so
its commutator is contained in the penultimate center, not excluded from it.

When the critical path has length three, the actual critical noncontainment
and the proved quotient-action kernel construct an actor meeting every
hypothesis of the proposed (9.5) residual exclusion. The involution action
on the elementary eight supplies the required index two. Thus a genuine
ambient context with initial center order four, length three, and terminal
module order eight suffices to refute that proposed exclusion.

No existence of such an ambient context is asserted here. In particular,
these conditional audit results neither prove the requested exclusion nor
constitute a full counterexample. The source allows order eight in (9.5)(a)
and names M12 as a (10.1)(a) example. Its intervening core-noncentrality claim
on printed p.53 requires independent verification against that example.

Source: refs/files/stellmacher-n-group.pdf, printed pp.52–53 and Section 10.
-/

namespace Stellmacher.SectionNine.ResidualNotCenterAudit

open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement

universe u

private theorem commutator_le_of_normalized_index_two
    {G : Type u} [Group G] (large small acting : Subgroup G)
    (hindex : (small.subgroupOf large).index = 2)
    (hlarge : acting ≤ Subgroup.normalizer (large : Set G))
    (hsmall : acting ≤ Subgroup.normalizer (small : Set G)) :
    ⁅large, acting⁆ ≤ small := by
  apply Subgroup.commutator_le.mpr
  intro vector hvector mover hmover
  have hconj : mover * vector⁻¹ * mover⁻¹ ∈ large :=
    (Subgroup.mem_normalizer_iff.mp (hlarge hmover) _).mp (large.inv_mem hvector)
  have hsame : (⟨vector, hvector⟩ : large) ∈ small.subgroupOf large ↔
      (⟨mover * vector⁻¹ * mover⁻¹, hconj⟩ : large) ∈ small.subgroupOf large := by
    change vector ∈ small ↔ mover * vector⁻¹ * mover⁻¹ ∈ small
    exact small.inv_mem_iff.symm.trans
      (Subgroup.mem_normalizer_iff.mp (hsmall hmover) _)
  have hmul := ((small.subgroupOf large).mul_mem_iff_of_index_two hindex).mpr hsame
  change vector * (mover * vector⁻¹ * mover⁻¹) ∈ small at hmul
  simpa only [commutatorElement_def, mul_assoc] using hmul

public theorem residual_le_penultimate_center_of_terminal_card_eight
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hb : 1 < ctx.criticalPath.length) (actor : G)
    (hactor : actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (height : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 8) :
    ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ≤
      ZAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) := by
  let penultimate := ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
    Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let moduleSubgroup := VAt ctx.Γ ctx.criticalPath.a'
  let center := ZAt ctx.Γ penultimate
  have hadj := nine_five_penultimate_adjacent ctx
  have hcenterModule : center ≤ moduleSubgroup := by
    change center ≤ VAt ctx.Γ ctx.criticalPath.a'
    rw [VAt, v, ctx.Γ.vAt_def]
    exact le_sSup ⟨_, (mem_neighborhood_iff_adjacent ctx.Γ).mpr
      (ctx.Γ.adjacent_symm hadj), rfl⟩
  have hcenterCard : Nat.card center = 4 := by
    obtain ⟨mover, hmiddle, _⟩ := lemma_seven_five_endpoint_alignment
      ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
    change ctx.Γ.act mover ctx.criticalPath.a = penultimate at hmiddle
    change Nat.card (z ctx.Γ penultimate) = 4
    rw [← hmiddle, z_act,
      Subgroup.card_map_of_injective (MulAut.conj mover⁻¹).injective]
    exact hfour
  have hindex : (center.subgroupOf moduleSubgroup).index = 2 := by
    have hcard := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcenterModule).toEquiv
    have hproduct := (center.subgroupOf moduleSubgroup).index_mul_card
    rw [hcard, hcenterCard] at hproduct
    change (center.subgroupOf moduleSubgroup).index * 4 =
      Nat.card (VAt ctx.Γ ctx.criticalPath.a') at hproduct
    rw [height] at hproduct
    omega
  have hcyclic : Subgroup.zpowers actor ≤ VAt ctx.Γ ctx.criticalPath.firstStep :=
    Subgroup.zpowers_le.mpr hactor
  have hterminal : Subgroup.zpowers actor ≤ GAt ctx.Γ ctx.criticalPath.a' :=
    hcyclic.trans
      (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.2
  have hcore : Subgroup.zpowers actor ≤ QAt ctx.Γ penultimate :=
    hcyclic.trans (nine_three_initial_extraction_inputs ctx hb).2.1
  have hlocal : QAt ctx.Γ penultimate ≤ GAt ctx.Γ penultimate := by
    rw [QAt, q, ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  exact commutator_le_of_normalized_index_two moduleSubgroup center _ hindex
    (hterminal.trans (stabilizer_le_normalizer_v ctx.Γ _))
    ((hcore.trans hlocal).trans (stabilizer_le_normalizer_z ctx.Γ _))

public theorem exists_small_case_actor_of_length_three
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hthree : ctx.criticalPath.length = 3)
    (height : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 8) :
    ∃ prev : ctx.Γ.Vertex,
      IsCriticalPathOffset ctx.Γ ctx.criticalPath (ctx.criticalPath.length - 2) prev ∧
      ∃ actor : G,
        (actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep ∧
          actor ∉ QAt ctx.Γ ctx.criticalPath.a') ∧
        QuotientCardEq
          (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
            ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2 ∧
        ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ≤ VAt ctx.Γ prev ∧
        ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ≤
          ZAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
            Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) := by
  have hb : 1 < ctx.criticalPath.length := by omega
  obtain ⟨actor, hactorInitial, hactorFirst, hactorOutside⟩ :=
    (nine_three_initial_extraction_inputs ctx.toLocalContext hb).2.2.2.2.2.2
  let residual := ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆
  let terminalLine := ZAt ctx.Γ ctx.criticalPath.a'
  have hcyclic : Subgroup.zpowers actor ≤ ZAt ctx.Γ ctx.criticalPath.a :=
    Subgroup.zpowers_le.mpr hactorInitial
  have hresidualGlobal := Subgroup.commutator_mono
    (show VAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.a' from le_rfl)
    hcyclic
  have hresidualModules := hresidualGlobal.trans
    (nine_seven_terminal_initial_commutator_le_modules ctx)
  obtain ⟨mover, _, hterminal⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep
      ctx.criticalPath.a' := ⟨mover, hterminal⟩
  obtain ⟨hlineCard, hmoduleComm⟩ := nine_next_center_and_commutator_of_initial_four
    ctx.toLocalContext hfour _ horbit
  have hkernel := (nine_next_v_module_kernel_of_center_and_commutator
    ctx hb _ horbit hlineCard hmoduleComm).2.2
  have hactorTerminal : actor ∈ GAt ctx.Γ ctx.criticalPath.a' :=
    (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.2
      hactorFirst
  have hnotLine : ¬ residual ≤ terminalLine := fun hle =>
    hactorOutside ((hkernel actor hactorTerminal).mp hle)
  have hresidualNe : residual ≠ ⊥ := fun heq => hnotLine (heq ▸ bot_le)
  have hresidualCard : Nat.card residual = 2 := by
    have hbound := Subgroup.card_le_of_le hresidualGlobal
    rw [nine_seven_terminal_initial_commutator_card_two ctx hb hfour height] at hbound
    change Nat.card residual ≤ 2 at hbound
    have hpositive := (Subgroup.one_lt_card_iff_ne_bot residual).mpr hresidualNe
    omega
  have hdisjoint : Disjoint residual terminalLine := by
    have hdiv := Subgroup.card_dvd_of_le
      (show residual ⊓ terminalLine ≤ residual from inf_le_left)
    rw [hresidualCard] at hdiv
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | htwo
    · exact disjoint_iff.mpr (Subgroup.eq_bot_of_card_eq _ hone)
    · have heq : residual ⊓ terminalLine = residual :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [htwo, hresidualCard])
      exact (hnotLine (heq ▸ inf_le_right)).elim
  have hlineModule : terminalLine ≤ VAt ctx.Γ ctx.criticalPath.a' := by
    apply (nine_five_penultimate_center_layer_of_initial_four ctx.toLocalContext hfour).1.trans
    rw [VAt, v, ctx.Γ.vAt_def]
    exact le_sSup ⟨_, (mem_neighborhood_iff_adjacent ctx.Γ).mpr
      (ctx.Γ.adjacent_symm (nine_five_penultimate_adjacent ctx.toLocalContext)), rfl⟩
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a') :=
    (nine_three_second_extraction_inputs ctx.toLocalContext hb).2.2.1
  have hnormal : terminalLine ≤ Subgroup.normalizer (residual : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    exact (hlineModule.trans (Subgroup.le_centralizer _)).trans
      (Subgroup.centralizer_le (hresidualModules.trans inf_le_right))
  have hindex : QuotientCardEq (residual ⊔ terminalLine) terminalLine 2 := by
    change Nat.card (residual ⊔ terminalLine : Subgroup G) = 2 * Nat.card terminalLine
    rw [Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint _ _ hnormal hdisjoint,
      hresidualCard]
  refine ⟨ctx.criticalPath.firstStep, ?_, actor,
    ⟨hactorFirst, hactorOutside⟩, hindex, hresidualModules.trans inf_le_left, ?_⟩
  · exact ⟨⟨1, by omega⟩, by dsimp; omega, ctx.criticalPath.path_first⟩
  · exact residual_le_penultimate_center_of_terminal_card_eight
      ctx.toLocalContext hfour hb actor hactorFirst height


end Stellmacher.SectionNine.ResidualNotCenterAudit
