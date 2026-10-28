module
public import Stellmacher.SectionNine.NineThreeNativeActionRank
public import Stellmacher.SectionNine.NineThreeBaumannCenterCommutator
public import Stellmacher.SectionNine.NineThreeMixedActor
public import Stellmacher.SectionNine.NineThreeMixedCanonicalFixed
public import Stellmacher.SectionOne.OneSevenCommutatorFixed
public import Stellmacher.SectionNine.NineThreeSourceNativeThompsonAction

/-!
# Quotient bridges for the source's barred Baumann reduction

The first theorem identifies the actual native Baumann image in the named
Section Six quotient, assuming nontrivial native Thompson action. The graph
wrapper retains the embedding and identifies this image with canonical oneB.
The mixed-collapse theorem shows that containment of the actual barred mixed actor in
oneB forces the restricted mixed commutator to vanish.

The final assembly proves R₁ = 1, nontrivial native Thompson action, the actual
barred Baumann identification, and exclusion of the mixed barred actor from
canonical oneB, without assuming any of these conclusions or a rank record.
The independent geometric prerequisites prove native action and restricted
mixed nontriviality; neither is inferred merely from nontriviality of the full
actor action. Source: Stellmacher (9.3),
printed pp.49–50/PDF pp.39–40 of refs/files/stellmacher-n-group.pdf. The printed
equation S-bar = B-bar (Z_m intersect G_a)-bar denotes a subgroup product,
not evaluation of a Baumann operator at the mixed actor.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

public theorem sixFour_source_native_baumann_image
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (hyp : HypothesisTwo H S0 S P1 P2)
    (hnative : ¬ elementaryAbelianMaxJ S ≤
      Subgroup.centralizer (sectionSixV S P1 : Set H)) :
    ((baumannIn S).subgroupOf P1).map (sectionSixQuotientMap hyp) =
      sectionSixBarredCritical hyp := by
  classical
  let sylow := sectionSixSylow hyp
  let quotient := sectionSixQuotientMap hyp
  have hsurj : Function.Surjective quotient := QuotientGroup.mk'_surjective _
  have hker : quotient.ker = SectionTwo.cSubgroup sylow := QuotientGroup.ker_mk' _
  let _ := sectionSixQuotientAction hyp
  have setup := sectionSix_barred_action_setup hyp
  have hsylow : (sylow : Subgroup P1).map P1.subtype = S := setup.sylow_image
  obtain ⟨hsolvable, hchar, _⟩ := lemma_five_three S0 S P1 P2 hyp
  have hnontrivial : (sylow : Subgroup P1) ≠ ⊥ := by
    intro hzero
    apply hyp.fiveOne.S_nontrivial
    rw [← hsylow, hzero, Subgroup.map_bot]
  have heven : 2 ∣ Nat.card sylow := sylow.isPGroup'.card_eq_or_dvd.resolve_left
    (fun hcard => hnontrivial (Subgroup.card_eq_one.mp hcard))
  have hsection : SectionTwo.Hypotheses P1 :=
    ⟨hsolvable, even_iff_two_dvd.mpr
      (heven.trans (sylow : Subgroup P1).card_subgroup_dvd_card), hchar⟩
  have hfamily := (pFamily_iff_pSet _ _ _).mp hyp.fiveOne.P1_mem
  have hcore : pCore 2 P1 ≠ ⊥ := by
    intro hzero
    apply hfamily.1.2.2.1
    change (pCore 2 P1).map P1.subtype = ⊥
    rw [hzero, Subgroup.map_bot]
  have hproper : (sylow : Subgroup P1) ≠ pCore 2 P1 := by
    intro heq
    apply hfamily.1.2.2.2
    rw [← hsylow, heq]
    rfl
  have hunique : IsUniqueMaximalContaining (sylow : Subgroup P1) (⊤ : Subgroup P1) :=
    native_uniqueMaximalContaining P1 (sylow : Subgroup P1)
      (by rw [hsylow]; exact hfamily.2)
  have hlocal : (⊤ : Subgroup P1) ∈ SectionThree.PSet ⊤ (sylow : Subgroup P1) := by
    have htransport := pFamily_range_of_injective (MonoidHom.id P1) Function.injective_id
      sylow (sylow : Subgroup P1) (Subgroup.map_id _) hcore hproper hunique
    rw [(MonoidHom.id P1).range_eq_top_of_surjective Function.surjective_id,
      pFamily_iff_pSet] at htransport
    exact htransport
  let thompson := elementaryAbelianMaxJ (sylow : Subgroup P1)
  let baumann := baumannIn (sylow : Subgroup P1)
  have hthompson : thompson.map P1.subtype = elementaryAbelianMaxJ S := by
    rw [← hsylow]
    exact (elementaryAbelianMaxJ_map_injective P1.subtype P1.subtype_injective _).symm
  have hbaumann : baumann.map P1.subtype = baumannIn S := by
    have hmap := baumann_map_injective P1.subtype P1.subtype_injective
      (sylow : Subgroup P1)
    change baumann.map P1.subtype = baumannIn ((sylow : Subgroup P1).map P1.subtype)
      at hmap
    exact hmap.trans (congrArg baumannIn hsylow)
  have himage : thompson.map quotient ≠ ⊥ := by
    intro hzero
    have hcentral : thompson ≤ SectionTwo.cSubgroup sylow := by
      rw [← hker]
      exact (Subgroup.map_eq_bot_iff thompson).mp hzero
    apply hnative
    rw [← hthompson]
    rintro _ ⟨actor, hactor, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro vector hvector
    rw [← setup.localV_image] at hvector
    obtain ⟨localVector, hlocalVector, rfl⟩ := hvector
    exact congrArg P1.subtype
      (Subgroup.mem_centralizer_iff.mp (hcentral hactor) localVector hlocalVector)
  have hidentify := SectionTwo.native_baumann_image_eq_global_oneJ_of_pSet
    hsection sylow hlocal quotient hsurj hker baumann rfl himage
  have hrestriction : (baumannIn S).subgroupOf P1 = baumann := by
    rw [← hbaumann]
    ext element
    constructor
    · rintro ⟨original, horiginal, heq⟩
      exact P1.subtype_injective heq ▸ horiginal
    · intro helement
      exact ⟨element, helement, rfl⟩
  rw [hrestriction]
  exact hidentify

end Stellmacher.SectionsFiveToSeven

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_three_source_native_baumann_identification_of_native_action
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (rank : NineThreeNativeActionRankData ctx)
    (hnative : ¬ elementaryAbelianMaxJ T ≤
      Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G)) :
    letI := rank.elementary
    letI := sectionSixQuotientAction ctx.hypothesisTwo
    (((baumannIn T).map embedding).subgroupOf P1).map
      (sectionSixQuotientMap ctx.hypothesisTwo) =
        SectionOne.oneB (V := sectionSixLocalV ctx.hypothesisTwo)
          (sectionSixBarSylow ctx.hypothesisTwo :
            Subgroup (SectionSixBarP1 ctx.hypothesisTwo)) := by
  let _ := rank.elementary
  let _ := sectionSixQuotientAction ctx.hypothesisTwo
  have hgroup : (GAt ctx.Γ ctx.criticalPath.a).map embedding = P1 :=
    (nine_two_ambient_setup ctx).2.1
  have hcenter : (ZAt ctx.Γ ctx.criticalPath.a).map embedding = sectionSixV S P1 :=
    nine_two_center_eq_sectionSixV ctx hgroup
  have hambient : ¬ elementaryAbelianMaxJ S ≤
      Subgroup.centralizer (sectionSixV S P1 : Set H) := by
    intro hcentral
    apply hnative
    intro actor hactor
    rw [Subgroup.mem_centralizer_iff]
    intro vector hvector
    apply ctx.embedding_injective
    have hactorImage : embedding actor ∈ elementaryAbelianMaxJ S := by
      rw [← ctx.map_S, elementaryAbelianMaxJ_map_injective
        embedding ctx.embedding_injective]
      exact Subgroup.mem_map_of_mem embedding hactor
    have hvectorImage : embedding vector ∈ sectionSixV S P1 :=
      hcenter ▸ Subgroup.mem_map_of_mem embedding hvector
    simpa only [map_mul] using
      Subgroup.mem_centralizer_iff.mp (hcentral hactorImage) (embedding vector) hvectorImage
  have hbaumann : (baumannIn T).map embedding = baumannIn S := by
    have hmap := baumann_map_injective embedding ctx.embedding_injective T
    change (baumannIn T).map embedding = baumannIn (T.map embedding) at hmap
    exact hmap.trans (congrArg baumannIn ctx.map_S)
  rw [hbaumann]
  rw [SectionOne.oneSeven_baumann_eq_j rank.action_hypotheses
    (sectionSixBarSylow ctx.hypothesisTwo)]
  exact sixFour_source_native_baumann_image ctx.hypothesisTwo hambient

public theorem nine_three_source_mixed_bot_of_barred_actor_le_oneB
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
    barActor ≤ SectionOne.oneB (V := sectionSixLocalV ctx.hypothesisTwo)
      (sectionSixBarSylow ctx.hypothesisTwo :
        Subgroup (SectionSixBarP1 ctx.hypothesisTwo)) →
      (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex, actor⁆ : Subgroup G) = ⊥ := by
  let _ := rank.elementary
  let _ := sectionSixQuotientAction ctx.hypothesisTwo
  let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let actor := ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a
  let barActor := ((actor.map embedding).subgroupOf P1).map
    (sectionSixQuotientMap ctx.hypothesisTwo)
  let moduleGroup := sectionSixLocalV ctx.hypothesisTwo
  let inclusion := P1.subtype.comp moduleGroup.subtype
  let plane := (⁅ZAt ctx.Γ ctx.criticalPath.a, actor⁆ : Subgroup G)
  let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex, actor⁆ : Subgroup G)
  let fixed := (Subgroup.centralizer
    (sectionSixBarredCriticalPreimage ctx.hypothesisTwo : Set H)).comap embedding
  change barActor ≤ SectionOne.oneB (V := moduleGroup)
    (sectionSixBarSylow ctx.hypothesisTwo : Subgroup (SectionSixBarP1 ctx.hypothesisTwo)) →
      mixed = ⊥
  intro hactor
  rw [SectionOne.oneSeven_baumann_eq_j rank.action_hypotheses
    (sectionSixBarSylow ctx.hypothesisTwo)] at hactor
  have hcomm : commutatorAction barActor moduleGroup ≤
      commutatorAction (sectionSixBarredCritical ctx.hypothesisTwo) moduleGroup := by
    rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
    apply Subgroup.closure_mono
    rintro displacement ⟨element, vector, rfl⟩
    exact ⟨⟨element, hactor element.property⟩, vector, rfl⟩
  have hfixed : commutatorAction barActor moduleGroup ≤
      FixedPoints.subgroup (sectionSixBarredCritical ctx.hypothesisTwo) moduleGroup :=
    hcomm.trans (SectionOne.oneSeven_commutator_le_fixed rank.action_hypotheses
      (sectionSixBarSylow ctx.hypothesisTwo))
  have hsylow := (nine_three_mixed_actor_quadratic ctx hb first second config).1
  have htransport := nine_three_barred_actor_critical_fixed_transport ctx actor hsylow
  change ((commutatorAction barActor moduleGroup) ⊓
    FixedPoints.subgroup (sectionSixBarredCritical ctx.hypothesisTwo) moduleGroup).map
      inclusion = (plane ⊓ fixed).map embedding at htransport
  rw [inf_eq_left.mpr hfixed] at htransport
  have hfull := (nine_three_barred_actor_action_transport ctx actor hsylow).2.2
  have heq : plane = plane ⊓ fixed := by
    apply (Subgroup.map_injective ctx.embedding_injective)
    exact hfull.symm.trans htransport
  have hzero := nine_three_mixed_canonical_fixed_bot
    ctx hb hlarge first second config rank.critical_ne_bot
  have hle : mixed ≤ fixed :=
    (Subgroup.commutator_mono inf_le_left le_rfl).trans (heq.le.trans inf_le_right)
  exact (inf_eq_left.mpr hle).symm.trans hzero

public theorem nine_three_source_barred_baumann_reduction
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second) :
    letI := sectionSixQuotientAction ctx.hypothesisTwo
    let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let actor := ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a
    let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex, actor⁆ : Subgroup G)
    let barActor := ((actor.map embedding).subgroupOf P1).map
      (sectionSixQuotientMap ctx.hypothesisTwo)
    let canonicalBaumann := SectionOne.oneB (V := sectionSixLocalV ctx.hypothesisTwo)
      (sectionSixBarSylow ctx.hypothesisTwo :
        Subgroup (SectionSixBarP1 ctx.hypothesisTwo))
    mixed ⊓ (Subgroup.center (baumannIn T)).map (baumannIn T).subtype = ⊥ ∧
      (¬ elementaryAbelianMaxJ T ≤
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G)) ∧
      (((baumannIn T).map embedding).subgroupOf P1).map
        (sectionSixQuotientMap ctx.hypothesisTwo) = canonicalBaumann ∧
      ¬ barActor ≤ canonicalBaumann := by
  let _ := sectionSixQuotientAction ctx.hypothesisTwo
  have hcritical := nine_three_canonical_offender_nontrivial ctx hb hlarge first second config
  have rank := nine_three_canonical_action_rank_data ctx hb hlarge first second config hcritical
  have hnative := nine_three_source_native_thompson_action ctx hb hlarge first second config
  refine ⟨nine_three_normalized_baumann_center_commutator_bot
    ctx hb hlarge first second config, hnative,
    nine_three_source_native_baumann_identification_of_native_action ctx rank hnative, ?_⟩
  intro hcontained
  exact nine_three_source_mixed_nontrivial ctx hb hlarge first second config
    (nine_three_source_mixed_bot_of_barred_actor_le_oneB
      ctx hb hlarge first second config rank hcontained)

public theorem nine_three_source_barred_actor_not_le_oneB
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second) :
    letI := sectionSixQuotientAction ctx.hypothesisTwo
    let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let actor := ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a
    ¬ ((actor.map embedding).subgroupOf P1).map
      (sectionSixQuotientMap ctx.hypothesisTwo) ≤
        SectionOne.oneB (V := sectionSixLocalV ctx.hypothesisTwo)
          (sectionSixBarSylow ctx.hypothesisTwo :
            Subgroup (SectionSixBarP1 ctx.hypothesisTwo)) :=
  (nine_three_source_barred_baumann_reduction ctx hb hlarge first second config).2.2.2

end Stellmacher.SectionNine
