module

public import Stellmacher.SectionNine.NineSevenLongDistanceSetup
public import Stellmacher.SectionNine.NineSevenShiftedIntersections
public import Stellmacher.SectionNine.NineNextCenterCommutator
public import Theory.GroupAction.ElementaryEightActorLine
public import Theory.GroupTheory.Commutator.IndexTwoSaturation
public import Theory.GroupTheory.SubgroupConjugation

/-!
# The commutator action and center bounds in Stellmacher (9.7)

The first-step center is a line in the initial center and centralizes the
terminal module by (7.4) and (7.5). Thus an involution outside that line
generates the same action commutator as the entire initial center. The
actual subgroup-conjugation action on the elementary eight has a fixed
plane of order four and a commutator line of order two. The exported
identification retains this exact action and its ambient subgroup image.

For adjacent vertices, an order-four center has index two in an order-eight
neighbor module. Both subgroups are normalized by the first vertex's core,
so their quotient has trivial core action. This bounds the module/core
commutator by the center. Applying this at the second and penultimate
vertices proves both required containments of the actual commutator R.
No containment of the entire core/module intersection is required.

The ambient hypotheses remain on H. Endpoint alignment supplies the
penultimate center order; the first-step and terminal module orders and
initial-orbit center orders suffice without further quotient-model or
intersection-index assumptions.

Source: Stellmacher, Journal of Algebra 190 (1997), printed p.53,
proof of (9.7), from "Assume that b > 3. Let R" through the symmetric
center bound; `refs/files/stellmacher-n-group.pdf`, PDF p.43.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement

universe u

public theorem nine_seven_normalized_index_two_commutator_le
    {G : Type u} [Group G] [Finite G] (large small actors : Subgroup G)
    (hindex : (small.subgroupOf large).index = 2)
    (hnlarge : actors ≤ Subgroup.normalizer (large : Set G))
    (hnsmall : actors ≤ Subgroup.normalizer (small : Set G)) :
    ⁅large, actors⁆ ≤ small := by
  apply Subgroup.commutator_le.mpr
  intro vector hvector actor hactor
  have hconj : actor * vector⁻¹ * actor⁻¹ ∈ large :=
    (Subgroup.mem_normalizer_iff.mp (hnlarge hactor) _).mp (large.inv_mem hvector)
  have hsame : (⟨vector, hvector⟩ : large) ∈ small.subgroupOf large ↔
      (⟨actor * vector⁻¹ * actor⁻¹, hconj⟩ : large) ∈ small.subgroupOf large := by
    change vector ∈ small ↔ actor * vector⁻¹ * actor⁻¹ ∈ small
    exact small.inv_mem_iff.symm.trans
      (Subgroup.mem_normalizer_iff.mp (hnsmall hactor) _)
  have hmul := ((small.subgroupOf large).mul_mem_iff_of_index_two hindex).mpr hsame
  change vector * (actor * vector⁻¹ * actor⁻¹) ∈ small at hmul
  simpa only [commutatorElement_def, mul_assoc] using hmul

public theorem nine_seven_neighbor_core_module_commutator_le_center
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    {middle neighbor : ctx.Γ.Vertex} (hadj : ctx.Γ.adjacent middle neighbor)
    (hmodule : Nat.card (VAt ctx.Γ neighbor) = 8)
    (hcenter : Nat.card (ZAt ctx.Γ middle) = 4) :
    ⁅VAt ctx.Γ neighbor, QAt ctx.Γ middle⁆ ≤ ZAt ctx.Γ middle := by
  have hle := nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hadj)
  have hindex : ((ZAt ctx.Γ middle).subgroupOf (VAt ctx.Γ neighbor)).index = 2 := by
    have hproduct := ((ZAt ctx.Γ middle).subgroupOf (VAt ctx.Γ neighbor)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      hmodule, hcenter] at hproduct
    omega
  have hcoreNeighbor := ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core
    middle neighbor ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj) default).2.2
  have hcoreSelf : QAt ctx.Γ middle ≤ GAt ctx.Γ middle := by
    rw [QAt, q, ctx.Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  exact nine_seven_normalized_index_two_commutator_le _ _ _ hindex
    (hcoreNeighbor.trans (stabilizer_le_normalizer_v ctx.Γ neighbor))
    (hcoreSelf.trans (stabilizer_le_normalizer_z ctx.Γ middle))

variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem nine_seven_commutator_cyclic_actor
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4) :
    ∃ actor : G, actor ∈ ZAt ctx.Γ ctx.criticalPath.a ∧
      (actor ≠ 1 ∧ actor ^ 2 = 1) ∧
      Subgroup.zpowers actor ≤ Subgroup.normalizer (VAt ctx.Γ ctx.criticalPath.a' : Set G) ∧
      ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ =
        ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ := by
  let initial := ZAt ctx.Γ ctx.criticalPath.a
  let line := ZAt ctx.Γ ctx.criticalPath.firstStep
  let terminal := VAt ctx.Γ ctx.criticalPath.a'
  have hcontain := lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath
  have hnext := (lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).next_center
  have hline : line ≤ initial := by
    change z ctx.Γ ctx.criticalPath.firstStep ≤ z ctx.Γ ctx.criticalPath.a
    rw [hnext.1]
    obtain ⟨_, sylow, hsylow⟩ := (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1
    rw [z, ctx.Γ.zAt_def]
    exact le_sSup ⟨sylow, congrArg omegaOneCenter hsylow.symm⟩
  have hlineCard : Nat.card line = 2 := nine_next_center_order_of_initial_four ctx.toLocalContext hfour
  have hlineCentral : line ≤ Subgroup.centralizer (terminal : Set G) := by
    change z ctx.Γ ctx.criticalPath.firstStep ≤ _
    rw [hnext.2]
    exact (omegaOneCenter_le_centerAmbient _).trans ((centerAmbient_le_centralizer _).trans
      (Subgroup.centralizer_le hcontain.reverse_containment.2))
  have hindex : line.relIndex initial = 2 := by
    have hproduct := (line.subgroupOf initial).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hline).toEquiv,
      hlineCard, hfour] at hproduct
    change (line.subgroupOf initial).index = 2
    omega
  have hnot : ¬ initial ≤ line := by
    intro hle
    have hcard := Subgroup.card_le_of_le hle
    rw [hfour, hlineCard] at hcard
    omega
  obtain ⟨actor, hactor, houtside⟩ := SetLike.not_le_iff_exists.mp hnot
  have hnorm : initial ≤ Subgroup.normalizer (terminal : Set G) :=
    (hcontain.first_containment.1.trans hcontain.first_containment.2).trans
      (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a')
  have hcyclic : Subgroup.zpowers actor ≤ initial := Subgroup.zpowers_le.mpr hactor
  have heq := Subgroup.commutator_eq_of_centralizing_index_two terminal line initial
    (Subgroup.zpowers actor) hnorm hline hlineCentral hindex hcyclic
    (fun hle => houtside (hle (Subgroup.mem_zpowers actor)))
  rw [Subgroup.commutator_comm initial, Subgroup.commutator_comm (Subgroup.zpowers actor)] at heq
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.firstStep) :=
    ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).longer_case hb).1
  exact ⟨actor, hactor, ⟨fun hone => houtside (hone ▸ line.one_mem),
    elemPow_eq_one_of_isElementaryAbelian actor (hcontain.first_containment.1 hactor)⟩,
    hcyclic.trans hnorm, heq⟩

public theorem nine_seven_terminal_initial_commutator_card_two
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hendCard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2 ^ 3) :
    Nat.card (⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G) = 2 := by
  obtain ⟨actor, _, hactor, hnorm, heq⟩ := nine_seven_commutator_cyclic_actor ctx hb hfour
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a') :=
    (nine_three_second_extraction_inputs ctx.toLocalContext hb).2.2.1
  have hne := nine_seven_terminal_initial_commutator_ne_bot ctx
  rw [heq] at hne ⊢
  exact Subgroup.involution_commutator_card_two_on_elementary_eight _ actor hactor hnorm hendCard hne

public theorem nine_seven_commutator_action_identification
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hendCard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2 ^ 3) :
    ∃ actor : G, actor ∈ ZAt ctx.Γ ctx.criticalPath.a ∧
      (actor ≠ 1 ∧ actor ^ 2 = 1) ∧
      ∃ hnormal : Subgroup.zpowers actor ≤
          Subgroup.normalizer (VAt ctx.Γ ctx.criticalPath.a' : Set G),
        let _ : Subgroup.Normalizes (Subgroup.zpowers actor)
            (VAt ctx.Γ ctx.criticalPath.a') := ⟨hnormal⟩
        (commutatorAction (Subgroup.zpowers actor) (VAt ctx.Γ ctx.criticalPath.a')).map
            (VAt ctx.Γ ctx.criticalPath.a').subtype =
          ⁅VAt ctx.Γ ctx.criticalPath.a', ZAt ctx.Γ ctx.criticalPath.a⁆ ∧
        Nat.card (FixedPoints.subgroup (Subgroup.zpowers actor)
          (VAt ctx.Γ ctx.criticalPath.a')) = 4 ∧
        Nat.card (commutatorAction (Subgroup.zpowers actor)
          (VAt ctx.Γ ctx.criticalPath.a')) = 2 := by
  obtain ⟨actor, hmem, hactor, hnormal, heq⟩ := nine_seven_commutator_cyclic_actor ctx hb hfour
  refine ⟨actor, hmem, hactor, hnormal, ?_⟩
  let moduleGroup := VAt ctx.Γ ctx.criticalPath.a'
  let actors := Subgroup.zpowers actor
  let _ : Subgroup.Normalizes actors moduleGroup := ⟨hnormal⟩
  let _ : IsElementaryAbelian 2 moduleGroup :=
    (nine_three_second_extraction_inputs ctx.toLocalContext hb).2.2.1
  let _ : Nontrivial moduleGroup := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1 < Nat.card (VAt ctx.Γ ctx.criticalPath.a')
    rw [hendCard]
    decide)
  have hmap := (commutatorAction_subgroup_conj_map_eq_commutator moduleGroup actors hnormal).trans heq.symm
  have hcard := nine_seven_terminal_initial_commutator_card_two ctx hb hfour hendCard
  rw [← hmap, Subgroup.card_map_of_injective moduleGroup.subtype_injective] at hcard
  have hactors : Nat.card actors = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hactor.2 hactor.1]
  let generator : actors := ⟨actor, Subgroup.mem_zpowers actor⟩
  have hgenerator : generator ≠ 1 ∧ generator ^ 2 = 1 :=
    ⟨fun heq => hactor.1 (congrArg Subtype.val heq), Subtype.ext hactor.2⟩
  have hproduct := (card_two_action_fixed_commutator_card_data
    (U := moduleGroup) generator hgenerator hactors).1
  change Nat.card moduleGroup = Nat.card (FixedPoints.subgroup actors moduleGroup) *
    Nat.card (commutatorAction actors moduleGroup) at hproduct
  rw [hcard, show Nat.card moduleGroup = 8 from hendCard] at hproduct
  have hfixed : Nat.card (FixedPoints.subgroup actors moduleGroup) = 4 := by omega
  exact ⟨hmap, hfixed, hcard⟩

set_option maxHeartbeats 800000 in
public theorem nine_seven_commutator_action_center_bridge
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hfirstCard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 2 ^ 3)
    (hendCard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2 ^ 3)
    (hstartCard : ∀ vertex, IsConjugateVertex ctx.Γ ctx.criticalPath.a vertex →
      Nat.card (ZAt ctx.Γ vertex) = 4) :
    let cp := ctx.criticalPath
    let commutator := ⁅VAt ctx.Γ cp.a', ZAt ctx.Γ cp.a⁆
    Nat.card commutator = 2 ∧
      commutator ≤ ZAt ctx.Γ (cp.path ⟨2, by dsimp [cp]; omega⟩) ∧
      commutator ≤ ZAt ctx.Γ (cp.path ⟨cp.length - 1, by dsimp [cp]; omega⟩) := by
  let cp := ctx.criticalPath
  let second := cp.path ⟨2, by dsimp [cp]; omega⟩
  let penultimate := cp.path ⟨cp.length - 1, by dsimp [cp]; omega⟩
  have hfirstSecond : ctx.Γ.adjacent cp.firstStep second := by
    have hadj := cp.path_adj ⟨1, by dsimp [cp]; omega⟩
    change ctx.Γ.adjacent (cp.path ⟨1, by dsimp [cp]; omega⟩) second at hadj
    rwa [cp.path_first] at hadj
  have hpenEnd : ctx.Γ.adjacent penultimate cp.a' := by
    have hadj := cp.path_adj ⟨cp.length - 1, by dsimp [cp]; omega⟩
    have hend : (⟨cp.length - 1, by dsimp [cp]; omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp [cp]
      omega
    rw [hend, cp.path_end] at hadj
    exact hadj
  obtain ⟨secondMover, hsecondMover⟩ :=
    (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity cp.firstStep
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm cp.firstStep_adj))
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirstSecond)
  have hsecondCard : Nat.card (ZAt ctx.Γ second) = 4 :=
    hstartCard second ⟨secondMover, hsecondMover⟩
  obtain ⟨endpointMover, hpenMover, _⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ cp ctx.commutator_eq
  have hpenCard : Nat.card (ZAt ctx.Γ penultimate) = 4 :=
    hstartCard penultimate ⟨endpointMover, hpenMover⟩
  have hinitialCard := hstartCard cp.a ⟨1, ctx.Γ.act_one cp.a⟩
  refine ⟨nine_seven_terminal_initial_commutator_card_two ctx hb hinitialCard hendCard, ?_, ?_⟩
  · have hbound := nine_seven_neighbor_core_module_commutator_le_center ctx.toLocalContext
      (ctx.Γ.adjacent_symm hfirstSecond) hfirstCard hsecondCard
    have hmodules : ⁅VAt ctx.Γ cp.a', ZAt ctx.Γ cp.a⁆ ≤
        ⁅VAt ctx.Γ cp.firstStep, VAt ctx.Γ cp.a'⁆ := by
      rw [Subgroup.commutator_comm (VAt ctx.Γ cp.firstStep)]
      exact Subgroup.commutator_mono le_rfl
        (lemma_seven_four ctx.sectionSeven ctx.Γ cp).first_containment.1
    exact hmodules.trans ((Subgroup.commutator_mono le_rfl
      (nine_three_second_extraction_inputs ctx.toLocalContext hb).2.1).trans hbound)
  · have hbound := nine_seven_neighbor_core_module_commutator_le_center ctx.toLocalContext
      hpenEnd hendCard hpenCard
    have hinitial := (lemma_seven_four ctx.sectionSeven ctx.Γ cp).first_containment.1.trans
      (nine_three_initial_extraction_inputs ctx.toLocalContext hb).2.1
    exact (Subgroup.commutator_mono le_rfl hinitial).trans hbound

end Stellmacher.SectionNine
