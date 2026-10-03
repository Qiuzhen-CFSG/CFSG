module
public import Stellmacher.SectionNine.NineThreeMixedActor
public import Stellmacher.SectionNine.NineThreeCanonicalOffenderNontrivial
public import Stellmacher.SectionNine.NineThreeCanonicalActionRank
public import Stellmacher.SectionNine.NineThreeCanonicalFixedGeneration
public import Stellmacher.SectionOne.OneSevenNoCentralTransvection

/-!
# The restricted mixed commutator in (9.3) is nontrivial

For the actual normalized pair, suppose that the restricted mixed commutator
vanishes. The first center hyperplane is then the full fixed subgroup of the
other-center actor: it has index two and the full action is nontrivial.
The quadratic fixed-index theorem puts the full commutator in the canonical
critical fixed space.

The second extracted group centralizes this full commutator. Its first
generating module is elementary and contains the commutator, while its
conjugate module lies in the initial core and centralizes the initial center.
The canonical (6.4) generation criterion therefore puts the full commutator
in the next center, which centralizes the distinguished Sylow.

In the canonical rank-two quotient the actor has order two, and fixed index
two makes its displacement a line. A Sylow-fixed displacement line cannot
occur with two factor supports: Sylow transitivity and disjoint supports
give the contradiction. No native Thompson nontriviality, barred exclusion,
mixed order, or final (9.3) conclusion is used.

Source: Stellmacher (9.3), printed pp.49–50/PDF pp.39–40,
`refs/files/stellmacher-n-group.pdf`. This proves only the nontriviality
part of the source's assertion that the actual mixed commutator has order two.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem source_fixed_hyperplane_of_mixed_bot
    {G : Type u} [Group G] [Finite G] (center stabilizer actor : Subgroup G)
    (hindex : Nat.card center = 2 * Nat.card (center ⊓ stabilizer : Subgroup G))
    (hzero : ⁅center ⊓ stabilizer, actor⁆ = ⊥)
    (hnontrivial : ¬ center ≤ Subgroup.centralizer (actor : Set G)) :
    center ⊓ Subgroup.centralizer (actor : Set G) = center ⊓ stabilizer := by
  let hyperplane := center ⊓ stabilizer
  let fixed := center ⊓ Subgroup.centralizer (actor : Set G)
  have hle : hyperplane ≤ fixed := le_inf inf_le_left
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hzero)
  have hproper : fixed ≠ center := fun heq =>
    hnontrivial (heq ▸ (inf_le_right : fixed ≤ Subgroup.centralizer (actor : Set G)))
  have hlt : Nat.card fixed < Nat.card center := by
    apply lt_of_le_of_ne (Subgroup.card_le_of_le inf_le_left)
    intro heq
    exact hproper (Subgroup.eq_of_le_of_card_ge inf_le_left heq.ge)
  obtain ⟨index, hcard⟩ := Subgroup.card_dvd_of_le (inf_le_left : fixed ≤ center)
  have hpositive : 0 < Nat.card fixed := Nat.card_pos
  have htwo : 2 ≤ index := by nlinarith
  have hbound : Nat.card fixed ≤ Nat.card hyperplane := by
    change Nat.card center = 2 * Nat.card hyperplane at hindex
    nlinarith
  exact (Subgroup.eq_of_le_of_card_ge hle hbound).symm

private theorem source_full_fixed_index_of_mixed_bot
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second)
    (hzero : let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
      (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
        ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G) = ⊥) :
    let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 2 * Nat.card
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer
        ((ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a : Subgroup G) : Set G) : Subgroup G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let conjugation := MulAut.conj config.g⁻¹
  let oldFirst := Γ.act first.extraction.x⁻¹ first.l
  let oldSecond := Γ.act second.extraction.x⁻¹ second.l
  let vertex := Γ.act config.g oldFirst
  have hcenter : (ZAt Γ oldSecond).map conjugation.toMonoidHom = ZAt Γ cp.a := by
    change (z Γ oldSecond).map (MulAut.conj config.g⁻¹).toMonoidHom = _
    rw [← z_act, config.maps_new_vertex]
  have hgroup : (GAt Γ oldFirst).map conjugation.toMonoidHom = GAt Γ vertex := by
    change conjugateBy (stabilizer Γ oldFirst) config.g⁻¹ = _
    rw [← stabilizer_act]
  have hindex : Nat.card (ZAt Γ cp.a) =
      2 * Nat.card (ZAt Γ cp.a ⊓ GAt Γ vertex : Subgroup G) := by
    rw [← hcenter, ← hgroup, ← Subgroup.map_inf _ _ _ conjugation.injective,
      Subgroup.card_map_of_injective conjugation.injective,
      Subgroup.card_map_of_injective conjugation.injective]
    exact (nine_three_four_center_indices ctx hb hlarge first second).2.2.1
  have heq := source_fixed_hyperplane_of_mixed_bot (ZAt Γ cp.a) (GAt Γ vertex)
    (ZAt Γ vertex ⊓ GAt Γ cp.a) hindex hzero
    (nine_three_mixed_actor_nontrivial_action ctx hb hlarge first second config)
  exact hindex.trans
    (congrArg (fun subgroup : Subgroup G => 2 * Nat.card subgroup) heq.symm)

private theorem source_second_extraction_centralizes_full_commutator
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second) :
    let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    second.E.map (MulAut.conj config.g⁻¹).toMonoidHom ≤ Subgroup.centralizer
      ((⁅ZAt ctx.Γ ctx.criticalPath.a,
        ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G) : Set G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let vertex := Γ.act config.g (Γ.act first.extraction.x⁻¹ first.l)
  let terminal := Γ.act config.g cp.a'
  let moduleGroup := VAt Γ terminal
  let actor := ZAt Γ vertex ⊓ GAt Γ cp.a
  let full := ⁅ZAt Γ cp.a, actor⁆
  have hcenter : ZAt Γ vertex ≤ moduleGroup := by
    change z Γ (Γ.act config.g (Γ.act first.extraction.x⁻¹ first.l)) ≤
      v Γ (Γ.act config.g cp.a')
    rw [z_act, v_act]
    apply Subgroup.map_mono
    rw [v, Γ.vAt_def]
    exact le_sSup ⟨_, first.extraction.neighbor, rfl⟩
  have hinitial : ZAt Γ cp.a ≤ GAt Γ terminal := by
    apply ((lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1).trans
    exact (config.first_geometry.generated.symm ▸ le_sup_left).trans
      config.first_geometry.group_le
  have hfullModule : full ≤ moduleGroup :=
    (Subgroup.commutator_mono le_rfl (inf_le_left.trans hcenter)).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp
        (hinitial.trans (stabilizer_le_normalizer_v Γ terminal)))
  have hfullCenter : full ≤ ZAt Γ cp.a :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (inf_le_right.trans (stabilizer_le_normalizer_z Γ cp.a))
  have helementary : IsElementaryAbelian 2 moduleGroup := by
    change IsElementaryAbelian 2 (v Γ (Γ.act config.g cp.a'))
    rw [v_act]
    let _ : IsElementaryAbelian 2 (v Γ cp.a') :=
      (nine_three_second_extraction_inputs ctx.toLocalContext hb).2.2.1
    exact IsElementaryAbelian.map (MulAut.conj config.g⁻¹).toMonoidHom
  let _ := helementary
  rw [config.second_geometry.generated]
  refine sup_le ?_ ?_
  · intro element helement
    rw [Subgroup.mem_centralizer_iff]
    intro point hpoint
    exact setLike_mul_comm (s := moduleGroup) (hfullModule hpoint) helement
  · have hcore := config.second_geometry.conjugate_core_le
    rw [config.second_new_vertex] at hcore
    have hneighbor : cp.firstStep ∈ neighborhood Γ cp.a :=
      (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
    have hcentral := ((lemma_seven_three ctx.sectionSeven Γ).center_core
      cp.a cp.firstStep hneighbor).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
    exact hcore.trans ((Subgroup.le_centralizer_iff.mp hcentral).trans
      (Subgroup.centralizer_le hfullCenter))

private theorem source_map_inf_centralizer
    {G H : Type*} [Group G] [Group H]
    (embedding : G →* H) (hinjective : Function.Injective embedding)
    (center actor : Subgroup G) :
    (center ⊓ Subgroup.centralizer (actor : Set G)).map embedding =
      center.map embedding ⊓ Subgroup.centralizer (actor.map embedding : Set H) := by
  apply le_antisymm
  · rintro _ ⟨point, hpoint, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem embedding hpoint.1, ?_⟩
    change embedding point ∈ Subgroup.centralizer (actor.map embedding : Set H)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨mover, hmover, rfl⟩
    simpa only [map_mul] using congrArg embedding
      (Subgroup.mem_centralizer_iff.mp hpoint.2 mover hmover)
  · rintro _ ⟨⟨point, hpoint, rfl⟩, hfixed⟩
    refine ⟨point, ⟨hpoint, ?_⟩, rfl⟩
    change point ∈ Subgroup.centralizer (actor : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro mover hmover
    apply hinjective
    simpa only [map_mul] using Subgroup.mem_centralizer_iff.mp hfixed
      (embedding mover) (Subgroup.mem_map_of_mem embedding hmover)

private theorem source_full_commutator_le_next_of_mixed_bot
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second)
    (hzero : let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
      (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
        ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G) = ⊥) :
    let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    (⁅ZAt ctx.Γ ctx.criticalPath.a,
      ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G) ≤
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let vertex := Γ.act config.g (Γ.act first.extraction.x⁻¹ first.l)
  let actor := ZAt Γ vertex ⊓ GAt Γ cp.a
  let extracted := second.E.map (MulAut.conj config.g⁻¹).toMonoidHom
  have haction := nine_three_mixed_actor_quadratic ctx hb first second config
  have hactor : actor.map embedding ≤ S := by
    rw [← ctx.map_S]
    exact Subgroup.map_mono haction.1
  have hcenter : (ZAt Γ cp.a).map embedding = sectionSixV S P1 :=
    nine_two_center_eq_sectionSixV ctx (nine_two_ambient_setup ctx).2.1
  have hindex : Nat.card (sectionSixV S P1) = 2 * Nat.card
      (sectionSixV S P1 ⊓ Subgroup.centralizer (actor.map embedding : Set H) : Subgroup H) := by
    rw [← hcenter, ← source_map_inf_centralizer embedding ctx.embedding_injective,
      Subgroup.card_map_of_injective ctx.embedding_injective,
      Subgroup.card_map_of_injective ctx.embedding_injective]
    exact source_full_fixed_index_of_mixed_bot ctx hb hlarge first second config hzero
  have hquadratic : ⁅⁅sectionSixV S P1, actor.map embedding⁆, actor.map embedding⁆ = ⊥ := by
    rw [← hcenter, ← Subgroup.map_commutator, ← Subgroup.map_commutator,
      haction.2, Subgroup.map_bot]
  have hfixed := sixFour_quadratic_index_two_barred_fixed ctx.hypothesisTwo
    (actor.map embedding) hactor hindex hquadratic
  have hfullCenter : ⁅ZAt Γ cp.a, actor⁆ ≤ ZAt Γ cp.a :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (inf_le_right.trans (stabilizer_le_normalizer_z Γ cp.a))
  have hgenerate : extracted ⊔ (GAt Γ cp.a ⊓ GAt Γ cp.firstStep) =
      GAt Γ cp.firstStep := by
    rw [inf_comm, ← config.second_new_vertex]
    exact config.second_geometry.edge_generated
  have hcentral := Subgroup.le_centralizer_iff.mp
    (source_second_extraction_centralizes_full_commutator ctx hb first second config)
  change ⁅ZAt Γ cp.a, actor⁆ ≤ ZAt Γ cp.firstStep
  intro point hpoint
  apply nine_three_canonical_fixed_generation ctx hfixed.1 extracted hgenerate point
    (hfullCenter hpoint) _ (hcentral hpoint)
  apply hfixed.2
  rw [← hcenter, ← Subgroup.map_commutator]
  exact Subgroup.mem_map_of_mem embedding hpoint

public theorem nine_three_source_mixed_nontrivial
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second) :
    let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
      ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G) ≠ ⊥ := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let vertex := Γ.act config.g (Γ.act first.extraction.x⁻¹ first.l)
  let actor := ZAt Γ vertex ⊓ GAt Γ cp.a
  change ⁅ZAt Γ cp.a ⊓ GAt Γ vertex, actor⁆ ≠ ⊥
  intro hzero
  have hcritical := nine_three_canonical_offender_nontrivial ctx hb hlarge first second config
  have rank := nine_three_canonical_action_rank_data ctx hb hlarge first second config hcritical
  let moduleGroup := sectionSixLocalV ctx.hypothesisTwo
  let barActor := ((actor.map embedding).subgroupOf P1).map
    (sectionSixQuotientMap ctx.hypothesisTwo)
  let inclusion := P1.subtype.comp moduleGroup.subtype
  let _ := rank.elementary
  let _ := sectionSixQuotientAction ctx.hypothesisTwo
  have hinjective : Function.Injective inclusion :=
    P1.subtype_injective.comp moduleGroup.subtype_injective
  have hmodule : Nat.card moduleGroup = 16 := by
    rw [← Subgroup.card_map_of_injective P1.subtype_injective,
      (sectionSix_barred_action_setup ctx.hypothesisTwo).localV_image,
      ← nine_two_center_eq_sectionSixV ctx (nine_two_ambient_setup ctx).2.1,
      Subgroup.card_map_of_injective ctx.embedding_injective, rank.center_card]
  let _ : Nontrivial moduleGroup := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hmodule]
    decide)
  have hcard : Nat.card barActor = 2 :=
    nine_three_mixed_barred_actor_card ctx hb hlarge first second config
  have htransport := nine_three_barred_actor_action_transport ctx actor
    (nine_three_mixed_actor_quadratic ctx hb first second config).1
  have hfixedCard : Nat.card (FixedPoints.subgroup barActor moduleGroup) =
      Nat.card (ZAt Γ cp.a ⊓ Subgroup.centralizer (actor : Set G) : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective hinjective, htransport.2.1,
      Subgroup.card_map_of_injective ctx.embedding_injective]
  have hindex := source_full_fixed_index_of_mixed_bot ctx hb hlarge first second config hzero
  change Nat.card (ZAt Γ cp.a) =
    2 * Nat.card (ZAt Γ cp.a ⊓ Subgroup.centralizer (actor : Set G) : Subgroup G) at hindex
  have hfixedEight : Nat.card (FixedPoints.subgroup barActor moduleGroup) = 8 := by
    rw [rank.center_card, ← hfixedCard] at hindex
    omega
  obtain ⟨involution, hne, _⟩ := (Nat.card_eq_two_iff' (1 : barActor)).mp hcard
  have hsquare : involution ^ 2 = 1 := by
    rw [← hcard]
    exact pow_card_eq_one' (x := involution)
  have hproduct := (card_two_action_fixed_commutator_card_data
    (U := moduleGroup) involution ⟨hne, hsquare⟩ hcard).1
  have hcommCard : Nat.card (commutatorAction barActor moduleGroup) = 2 := by
    rw [hmodule, hfixedEight] at hproduct
    omega
  apply SectionOne.oneSeven_rank_one_not_sylow_fixed rank.action_hypotheses
    (sectionSixBarSylow ctx.hypothesisTwo) rank.generated rank.unique_maximal
    rank.factor_count barActor htransport.1 hcard hcommCard
  have hsylowImage : ((T.map embedding).subgroupOf P1).map
      (sectionSixQuotientMap ctx.hypothesisTwo) =
      (sectionSixBarSylow ctx.hypothesisTwo : Subgroup _) := by
    have hlocal : (T.map embedding).subgroupOf P1 =
        (sectionSixSylow ctx.hypothesisTwo : Subgroup P1) := by
      apply Subgroup.map_injective P1.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le,
        (sectionSix_barred_action_setup ctx.hypothesisTwo).sylow_image, ctx.map_S]
      rw [ctx.map_S]
      exact ctx.hypothesisTwo.fiveOne.P1_mem.1.2.1.1
    rw [hlocal]
    rfl
  have hsylowTransport := (nine_three_barred_actor_action_transport ctx T le_rfl).2.1
  rw [hsylowImage] at hsylowTransport
  apply (Subgroup.map_le_map_iff_of_injective hinjective).mp
  rw [htransport.2.2, hsylowTransport]
  apply Subgroup.map_mono
  have hfullCenter : ⁅ZAt Γ cp.a, actor⁆ ≤ ZAt Γ cp.a :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (inf_le_right.trans (stabilizer_le_normalizer_z Γ cp.a))
  refine le_inf hfullCenter ?_
  have hnext := source_full_commutator_le_next_of_mixed_bot ctx hb hlarge first second config hzero
  have hcentral : ZAt Γ cp.firstStep ≤ Subgroup.centralizer (T : Set G) := by
    rw [show ZAt Γ cp.firstStep = omegaOneCenter T from
      (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).next_center.1]
    exact (omegaOneCenter_le_centerAmbient T).trans (centerAmbient_le_centralizer T)
  exact hnext.trans hcentral


end Stellmacher.SectionNine
