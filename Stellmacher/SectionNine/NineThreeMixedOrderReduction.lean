module
public import Stellmacher.SectionNine.NineThreeMixedActor
public import Stellmacher.SectionNine.NineThreeMixedCanonicalFixed
public import Theory.GroupAction.FourElementInvolutionLines

/-!
# Mixed order two from the actual commutator-plane cardinalities

The actual barred actor has order two. Rank-nullity for its canonical
action transports back to the native initial center and gives a fixed
subgroup of order four when the full commutator plane has order four.
The geometric hyperplane has order eight, so its mixed commutator is
nontrivial. The canonical fixed line in the full plane is disjoint from
the mixed subgroup, bounding the mixed order by two.

The plane-cardinality premises remain explicit. This is an assembly
reduction, not the unconditional mixed-order and barred-generation theorem.
Source: Stellmacher (9.3), printed p.50, `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_three_mixed_actor_fixed_card_of_plane_card
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second)
    (rank : NineThreeNativeActionRankData ctx)
    (hplane : Nat.card (⁅ZAt ctx.Γ ctx.criticalPath.a,
      ZAt ctx.Γ (ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)) ⊓
        GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G) = 4) :
    let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let actor := ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a
    Nat.card (ZAt ctx.Γ ctx.criticalPath.a ⊓
      Subgroup.centralizer (actor : Set G) : Subgroup G) = 4 := by
  let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let actor := ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a
  let moduleGroup := sectionSixLocalV ctx.hypothesisTwo
  let barActor := ((actor.map embedding).subgroupOf P1).map
    (sectionSixQuotientMap ctx.hypothesisTwo)
  let inclusion := P1.subtype.comp moduleGroup.subtype
  let _ := rank.elementary
  let _ := sectionSixQuotientAction ctx.hypothesisTwo
  have hinj : Function.Injective inclusion :=
    P1.subtype_injective.comp moduleGroup.subtype_injective
  have hcard : Nat.card barActor = 2 :=
    nine_three_mixed_barred_actor_card ctx hb hlarge first second config
  have hmodule : Nat.card moduleGroup = 16 := by
    rw [← Subgroup.card_map_of_injective P1.subtype_injective,
      (sectionSix_barred_action_setup ctx.hypothesisTwo).localV_image,
      ← nine_two_center_eq_sectionSixV ctx (nine_two_ambient_setup ctx).2.1,
      Subgroup.card_map_of_injective ctx.embedding_injective, rank.center_card]
  let _ : Nontrivial moduleGroup := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hmodule]
    decide)
  obtain ⟨involution, hne, _⟩ := (Nat.card_eq_two_iff' (1 : barActor)).mp hcard
  have hsquare : involution ^ 2 = 1 := by
    rw [← hcard]
    exact pow_card_eq_one' (x := involution)
  have hproduct := (card_two_action_fixed_commutator_card_data
    (U := moduleGroup) involution ⟨hne, hsquare⟩ hcard).1
  have htransport := nine_three_barred_actor_action_transport ctx actor
    (nine_three_mixed_actor_quadratic ctx hb first second config).1
  have hcommCard : Nat.card (commutatorAction barActor moduleGroup) = 4 := by
    rw [← Subgroup.card_map_of_injective hinj, htransport.2.2,
      Subgroup.card_map_of_injective ctx.embedding_injective]
    exact hplane
  have hfixedCard : Nat.card (FixedPoints.subgroup barActor moduleGroup) =
      Nat.card (ZAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (actor : Set G) : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective hinj, htransport.2.1,
      Subgroup.card_map_of_injective ctx.embedding_injective]
  rw [hmodule, hcommCard, hfixedCard] at hproduct
  change Nat.card (ZAt ctx.Γ ctx.criticalPath.a ⊓
    Subgroup.centralizer (actor : Set G) : Subgroup G) = 4
  omega

private theorem card_two_of_disjoint_line
    {G : Type*} [Group G] [Finite G] (mixed plane fixed : Subgroup G)
    (hcontain : mixed ≤ plane) (hplane : Nat.card plane = 4)
    (hline : Nat.card (plane ⊓ fixed : Subgroup G) = 2)
    (hdisjoint : mixed ⊓ fixed = ⊥) (hne : mixed ≠ ⊥) : Nat.card mixed = 2 := by
  have hindex := ((plane ⊓ fixed).subgroupOf plane).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show plane ⊓ fixed ≤ plane from inf_le_left)).toEquiv] at hindex
  change (plane ⊓ fixed).relIndex plane * Nat.card (plane ⊓ fixed : Subgroup G) =
    Nat.card plane at hindex
  rw [Subgroup.inf_relIndex_left, hline, hplane] at hindex
  have hindexTwo : fixed.relIndex plane = 2 := by omega
  have hbound := Subgroup.relIndex_le_of_le_right (H := fixed) hcontain
    (by rw [hindexTwo]; decide)
  rw [← Subgroup.inf_relIndex_left, hdisjoint, Subgroup.relIndex_bot_left] at hbound
  have hlower := (Subgroup.one_lt_card_iff_ne_bot mixed).mpr hne
  omega

public theorem nine_three_mixed_order_two_of_plane_cards
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second)
    (rank : NineThreeNativeActionRankData ctx) :
    let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let actor := ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a
    let plane := (⁅ZAt ctx.Γ ctx.criticalPath.a, actor⁆ : Subgroup G)
    let fixed := (Subgroup.centralizer
      (sectionSixBarredCriticalPreimage ctx.hypothesisTwo : Set H)).comap embedding
    Nat.card plane = 4 → Nat.card (plane ⊓ fixed : Subgroup G) = 2 →
      Nat.card (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex, actor⁆ : Subgroup G) = 2 := by
  let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let actor := ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a
  let hyperplane := ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex
  let mixed := (⁅hyperplane, actor⁆ : Subgroup G)
  change Nat.card (⁅ZAt ctx.Γ ctx.criticalPath.a, actor⁆ : Subgroup G) = 4 →
    Nat.card ((⁅ZAt ctx.Γ ctx.criticalPath.a, actor⁆ : Subgroup G) ⊓
      (Subgroup.centralizer
        (sectionSixBarredCriticalPreimage ctx.hypothesisTwo : Set H)).comap embedding :
          Subgroup G) = 2 → Nat.card mixed = 2
  intro hplane hline
  have hfixed := nine_three_mixed_actor_fixed_card_of_plane_card
    ctx hb hlarge first second config rank hplane
  have hhyper := (nine_three_mixed_hyperplane_and_overlap
    ctx hb hlarge first second config rank).1
  have hnontrivial : mixed ≠ ⊥ := by
    intro hzero
    have hcentral := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hzero
    have hbound := Subgroup.card_le_of_le
      (le_inf (show hyperplane ≤ ZAt ctx.Γ ctx.criticalPath.a from inf_le_left) hcentral)
    rw [hfixed] at hbound
    change Nat.card hyperplane = 8 at hhyper
    omega
  exact card_two_of_disjoint_line mixed _ _
    (Subgroup.commutator_mono inf_le_left le_rfl) hplane hline
    (nine_three_mixed_canonical_fixed_bot ctx hb hlarge first second config rank.critical_ne_bot)
    hnontrivial

public theorem nine_three_mixed_order_two_of_canonical_plane_cards
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second)
    (rank : NineThreeNativeActionRankData ctx) :
    letI := rank.elementary
    letI := sectionSixQuotientAction ctx.hypothesisTwo
    let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let actor := ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a
    let barActor := ((actor.map embedding).subgroupOf P1).map
      (sectionSixQuotientMap ctx.hypothesisTwo)
    let plane := commutatorAction barActor (sectionSixLocalV ctx.hypothesisTwo)
    let baumann := SectionOne.oneB (V := sectionSixLocalV ctx.hypothesisTwo)
      (sectionSixBarSylow ctx.hypothesisTwo : Subgroup (SectionSixBarP1 ctx.hypothesisTwo))
    Nat.card plane = 4 →
      Nat.card (plane ⊓ FixedPoints.subgroup baumann (sectionSixLocalV ctx.hypothesisTwo) :
        Subgroup (sectionSixLocalV ctx.hypothesisTwo)) = 2 →
      Nat.card (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex, actor⁆ : Subgroup G) = 2 := by
  let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let actor := ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a
  let moduleGroup := sectionSixLocalV ctx.hypothesisTwo
  let barActor := ((actor.map embedding).subgroupOf P1).map
    (sectionSixQuotientMap ctx.hypothesisTwo)
  let inclusion := P1.subtype.comp moduleGroup.subtype
  let _ := rank.elementary
  let _ := sectionSixQuotientAction ctx.hypothesisTwo
  change Nat.card (commutatorAction barActor moduleGroup) = 4 →
    Nat.card (commutatorAction barActor moduleGroup ⊓ FixedPoints.subgroup
      (SectionOne.oneB (V := moduleGroup) (sectionSixBarSylow ctx.hypothesisTwo :
        Subgroup (SectionSixBarP1 ctx.hypothesisTwo)))
        moduleGroup : Subgroup moduleGroup) = 2 → _
  intro hplane hline
  have hinj : Function.Injective inclusion :=
    P1.subtype_injective.comp moduleGroup.subtype_injective
  have hactor := (nine_three_mixed_actor_quadratic ctx hb first second config).1
  have hbaumann : SectionOne.oneB (V := moduleGroup)
      (sectionSixBarSylow ctx.hypothesisTwo : Subgroup (SectionSixBarP1 ctx.hypothesisTwo)) =
        sectionSixBarredCritical ctx.hypothesisTwo :=
    SectionOne.oneSeven_baumann_eq_j rank.action_hypotheses (sectionSixBarSylow ctx.hypothesisTwo)
  rw [hbaumann] at hline
  have hplaneMap := congrArg (fun subgroup : Subgroup H => Nat.card subgroup)
    (nine_three_barred_actor_action_transport ctx actor hactor).2.2
  rw [Subgroup.card_map_of_injective hinj,
    Subgroup.card_map_of_injective ctx.embedding_injective] at hplaneMap
  have hfixedMap := congrArg (fun subgroup : Subgroup H => Nat.card subgroup)
    (nine_three_barred_actor_critical_fixed_transport ctx actor hactor)
  rw [Subgroup.card_map_of_injective hinj,
    Subgroup.card_map_of_injective ctx.embedding_injective] at hfixedMap
  exact nine_three_mixed_order_two_of_plane_cards ctx hb hlarge first second config rank
    (hplaneMap.symm.trans hplane) (hfixedMap.symm.trans hline)

end Stellmacher.SectionNine
