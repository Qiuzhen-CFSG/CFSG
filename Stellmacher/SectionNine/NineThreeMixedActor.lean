module
public import Stellmacher.SectionNine.NineThreeMixedGeometry
public import Stellmacher.SectionNine.NineTwoCenterSectionSixModule
public import Stellmacher.SectionTwo.QuotientModuleTransport

/-!
# The actual mixed actor in the canonical Section Six quotient

The exact first-extraction inner index, transported through the supplied
normalization, gives index two over the initial-center action kernel.
The named Section Six quotient kills exactly that kernel, so the literal
barred actor has order two. Its Sylow containment, fixed space, and full
commutator transport retain the actual embedding and canonical action.

These are inputs to the still separate barred-generation and mixed-order
argument, not a substitute for that conjunction. Source: Stellmacher (9.3),
printed pp.49–50, `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem map_inf_centralizer
    {G H : Type*} [Group G] [Group H]
    (hom : G →* H) (hinj : Function.Injective hom) (left right : Subgroup G) :
    (left ⊓ Subgroup.centralizer (right : Set G)).map hom =
      left.map hom ⊓ Subgroup.centralizer (right.map hom : Set H) := by
  apply le_antisymm
  · rintro _ ⟨element, helement, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem hom helement.1, ?_⟩
    change hom element ∈ Subgroup.centralizer (right.map hom : Set H)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨actor, hactor, rfl⟩
    simpa only [map_mul] using congrArg hom
      (Subgroup.mem_centralizer_iff.mp helement.2 actor hactor)
  · rintro _ ⟨⟨element, helement, rfl⟩, hcentral⟩
    refine ⟨element, ⟨helement, ?_⟩, rfl⟩
    change element ∈ Subgroup.centralizer (right : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro actor hactor
    apply hinj
    simpa only [map_mul] using Subgroup.mem_centralizer_iff.mp hcentral
      (hom actor) (Subgroup.mem_map_of_mem hom hactor)

public theorem nine_three_mixed_actor_centralizer_index
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
    let actor := ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a
    Nat.card actor = 2 * Nat.card
      (actor ⊓ Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G) : Subgroup G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let conjugation := MulAut.conj config.g⁻¹
  let oldFirst := Γ.act first.extraction.x⁻¹ first.l
  let oldSecond := Γ.act second.extraction.x⁻¹ second.l
  let vertex := Γ.act config.g oldFirst
  let actor := ZAt Γ vertex ⊓ GAt Γ cp.a
  have hgroup : (GAt Γ oldSecond).map conjugation.toMonoidHom = GAt Γ cp.a := by
    change conjugateBy (stabilizer Γ oldSecond) config.g⁻¹ = _
    rw [← stabilizer_act, config.maps_new_vertex]
  have hcore : (QAt Γ oldSecond).map conjugation.toMonoidHom = QAt Γ cp.a := by
    change (q Γ oldSecond).map (MulAut.conj config.g⁻¹).toMonoidHom = _
    rw [← q_act, config.maps_new_vertex]
  have hcenter : (ZAt Γ oldFirst).map conjugation.toMonoidHom = ZAt Γ vertex := by
    change (z Γ oldFirst).map (MulAut.conj config.g⁻¹).toMonoidHom = _
    rw [← z_act]
  have hold : (ZAt Γ first.l).map conjugation.toMonoidHom =
      ZAt Γ (Γ.act config.g first.l) := by
    change (z Γ first.l).map (MulAut.conj config.g⁻¹).toMonoidHom = _
    rw [← z_act]
  have hintersection : ZAt Γ vertex ⊓ QAt Γ cp.a =
      ZAt Γ vertex ⊓ ZAt Γ (Γ.act config.g first.l) := by
    rw [← hcenter, ← hcore, ← hold,
      ← Subgroup.map_inf _ _ _ conjugation.injective,
      ← Subgroup.map_inf _ _ _ conjugation.injective]
    exact congrArg (Subgroup.map conjugation.toMonoidHom)
      (nine_three_first_relations_at_second_neighbor ctx hb hlarge first second).1
  have hindex : Nat.card actor =
      2 * Nat.card (ZAt Γ vertex ⊓ QAt Γ cp.a : Subgroup G) := by
    rw [hintersection]
    change Nat.card (ZAt Γ vertex ⊓ GAt Γ cp.a : Subgroup G) = _
    rw [← hcenter, ← hgroup, ← hold,
      ← Subgroup.map_inf _ _ _ conjugation.injective,
      ← Subgroup.map_inf _ _ _ conjugation.injective,
      Subgroup.card_map_of_injective conjugation.injective,
      Subgroup.card_map_of_injective conjugation.injective]
    exact (nine_three_four_center_indices ctx hb hlarge first second).2.1
  have hactor : actor ≤ T := (nine_three_mixed_actor_quadratic ctx hb first second config).1
  have hcentral : actor ⊓ Subgroup.centralizer (ZAt Γ cp.a : Set G) =
      ZAt Γ vertex ⊓ QAt Γ cp.a := by
    have hedge := (lemma_seven_four ctx.sectionSeven Γ cp).edge_centralizer
    change T ⊓ Subgroup.centralizer (ZAt Γ cp.a : Set G) = QAt Γ cp.a at hedge
    rw [← hedge]
    apply le_antisymm
    · exact fun element helement => ⟨helement.1.1, hactor helement.1, helement.2⟩
    · intro element helement
      exact ⟨⟨helement.1, (edge_sylow_data ctx.sectionSeven Γ cp).1.1 helement.2.1⟩,
        helement.2.2⟩
  change Nat.card actor = _
  rwa [hcentral]

public theorem nine_three_barred_actor_card_mul_kernel
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (actor : Subgroup G) (hactor : actor ≤ T) :
    let barActor := ((actor.map embedding).subgroupOf P1).map
      (sectionSixQuotientMap ctx.hypothesisTwo)
    Nat.card (actor ⊓ Subgroup.centralizer
      (ZAt ctx.Γ ctx.criticalPath.a : Set G) : Subgroup G) * Nat.card barActor =
        Nat.card actor := by
  let hypothesis := ctx.hypothesisTwo
  let quotient := sectionSixQuotientMap hypothesis
  let moduleGroup := sectionSixLocalV hypothesis
  let localActor := (actor.map embedding).subgroupOf P1
  have hsetup := sectionSix_barred_action_setup hypothesis
  have hcenter : (ZAt ctx.Γ ctx.criticalPath.a).map embedding = sectionSixV S P1 :=
    nine_two_center_eq_sectionSixV ctx (nine_two_ambient_setup ctx).2.1
  have hambient : actor.map embedding ≤ S := by
    rw [← ctx.map_S]
    exact Subgroup.map_mono hactor
  have hlocal : localActor.map P1.subtype = actor.map embedding :=
    Subgroup.map_subgroupOf_eq_of_le (hambient.trans hypothesis.fiveOne.P1_mem.1.2.1.1)
  have hkernel : quotient.ker = Subgroup.centralizer (moduleGroup : Set P1) :=
    QuotientGroup.ker_mk' _
  have hkernelMap : (localActor ⊓ quotient.ker).map P1.subtype =
      (actor ⊓ Subgroup.centralizer
        (ZAt ctx.Γ ctx.criticalPath.a : Set G)).map embedding := by
    rw [hkernel, map_inf_centralizer P1.subtype P1.subtype_injective,
      hlocal, hsetup.localV_image,
      map_inf_centralizer embedding ctx.embedding_injective, hcenter]
  have hkernelCard : Nat.card (localActor ⊓ quotient.ker : Subgroup P1) =
      Nat.card (actor ⊓ Subgroup.centralizer
        (ZAt ctx.Γ ctx.criticalPath.a : Set G) : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective P1.subtype_injective, hkernelMap,
      Subgroup.card_map_of_injective ctx.embedding_injective]
  have hactorCard : Nat.card localActor = Nat.card actor := by
    rw [← Subgroup.card_map_of_injective P1.subtype_injective, hlocal,
      Subgroup.card_map_of_injective ctx.embedding_injective]
  have hmul : Nat.card (localActor ⊓ quotient.ker : Subgroup P1) *
      Nat.card (localActor.map quotient) = Nat.card localActor := by
    rw [← Subgroup.relIndex_ker, ← Subgroup.inf_relIndex_left]
    simpa only [Subgroup.relIndex_bot_left] using
      Subgroup.relIndex_mul_relIndex (⊥ : Subgroup P1) (localActor ⊓ quotient.ker)
        localActor bot_le inf_le_left
  rw [hkernelCard, hactorCard] at hmul
  exact hmul

public theorem nine_three_mixed_barred_actor_card
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
    let actor := ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a
    Nat.card (((actor.map embedding).subgroupOf P1).map
      (sectionSixQuotientMap ctx.hypothesisTwo)) = 2 := by
  let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let actor := ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a
  have hmul := nine_three_barred_actor_card_mul_kernel ctx actor
    (nine_three_mixed_actor_quadratic ctx hb first second config).1
  have hindex := nine_three_mixed_actor_centralizer_index ctx hb hlarge first second config
  change Nat.card actor = _ at hindex
  rw [hindex, mul_comm 2] at hmul
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul

private theorem quotient_commutator_image_map
    {K X : Type u} [Group K] [Group X]
    (sylow : Sylow 2 K) (quotient : K →* X) (hsurj : Function.Surjective quotient)
    (hkernel : quotient.ker = SectionTwo.cSubgroup sylow) (actor : Subgroup K) :
    letI := SectionTwo.quotientConjugationAction sylow quotient hsurj hkernel
    (commutatorAction (actor.map quotient) (SectionTwo.vSubgroup sylow)).map
      (SectionTwo.vSubgroup sylow).subtype = ⁅SectionTwo.vSubgroup sylow, actor⁆ := by
  let moduleGroup := SectionTwo.vSubgroup sylow
  let _ := SectionTwo.quotientConjugationAction sylow quotient hsurj hkernel
  let _ : moduleGroup.Normal := Subgroup.normalClosure_normal
  have hnormal : actor ≤ Subgroup.normalizer (moduleGroup : Set K) :=
    Subgroup.le_normalizer_of_normal
  let _ : Subgroup.Normalizes actor moduleGroup := ⟨hnormal⟩
  have heq : commutatorAction (actor.map quotient) moduleGroup =
      commutatorAction actor moduleGroup := by
    rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
    congr 1
    ext displacement
    constructor
    · rintro ⟨imageActor, vector, rfl⟩
      obtain ⟨preimage, hpreimage, heq⟩ := imageActor.property
      refine ⟨⟨preimage, hpreimage⟩, vector, ?_⟩
      congr 1
      apply Subtype.ext
      change ((imageActor.val • vector : moduleGroup) : K) =
        preimage * (vector : K) * preimage⁻¹
      rw [← heq, SectionTwo.quotientConjugationAction_smul_coe sylow quotient hsurj hkernel]
    · rintro ⟨nativeActor, vector, rfl⟩
      refine ⟨⟨quotient nativeActor, Subgroup.mem_map_of_mem quotient nativeActor.property⟩,
        vector, ?_⟩
      congr 1
      apply Subtype.ext
      change (nativeActor : K) * (vector : K) * (nativeActor : K)⁻¹ =
        ((quotient nativeActor • vector : moduleGroup) : K)
      rw [SectionTwo.quotientConjugationAction_smul_coe sylow quotient hsurj hkernel]
  rw [heq, commutatorAction_subgroup_conj_map_eq_commutator moduleGroup actor hnormal]

public theorem nine_three_barred_actor_action_transport
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (actor : Subgroup G) (hactor : actor ≤ T) :
    letI := sectionSixQuotientAction ctx.hypothesisTwo
    let moduleGroup := sectionSixLocalV ctx.hypothesisTwo
    let barActor := ((actor.map embedding).subgroupOf P1).map
      (sectionSixQuotientMap ctx.hypothesisTwo)
    let inclusion := P1.subtype.comp moduleGroup.subtype
    barActor ≤ (sectionSixBarSylow ctx.hypothesisTwo : Subgroup _) ∧
      (FixedPoints.subgroup barActor moduleGroup).map inclusion =
        (ZAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer (actor : Set G)).map embedding ∧
      (commutatorAction barActor moduleGroup).map inclusion =
        (⁅ZAt ctx.Γ ctx.criticalPath.a, actor⁆ : Subgroup G).map embedding := by
  let hypothesis := ctx.hypothesisTwo
  let quotient := sectionSixQuotientMap hypothesis
  let moduleGroup := sectionSixLocalV hypothesis
  let localActor := (actor.map embedding).subgroupOf P1
  let _ := sectionSixQuotientAction hypothesis
  have hsetup := sectionSix_barred_action_setup hypothesis
  have hsurj : Function.Surjective quotient := QuotientGroup.mk'_surjective _
  have hkernel : quotient.ker = SectionTwo.cSubgroup (sectionSixSylow hypothesis) :=
    QuotientGroup.ker_mk' _
  have hcenter : (ZAt ctx.Γ ctx.criticalPath.a).map embedding = sectionSixV S P1 :=
    nine_two_center_eq_sectionSixV ctx (nine_two_ambient_setup ctx).2.1
  have hambient : actor.map embedding ≤ S := by
    rw [← ctx.map_S]
    exact Subgroup.map_mono hactor
  have hlocal : localActor.map P1.subtype = actor.map embedding :=
    Subgroup.map_subgroupOf_eq_of_le (hambient.trans hypothesis.fiveOne.P1_mem.1.2.1.1)
  refine ⟨?_, ?_, ?_⟩
  · apply Subgroup.map_mono
    apply (Subgroup.map_le_map_iff_of_injective P1.subtype_injective).mp
    rw [hlocal, hsetup.sylow_image]
    exact hambient
  · rw [← Subgroup.map_map]
    rw [SectionTwo.quotientConjugationAction_fixedPoints_image_map
      (sectionSixSylow hypothesis) quotient hsurj hkernel localActor]
    rw [map_inf_centralizer P1.subtype P1.subtype_injective,
      hsetup.localV_image, hlocal,
      map_inf_centralizer embedding ctx.embedding_injective, hcenter]
  · rw [← Subgroup.map_map]
    rw [quotient_commutator_image_map (sectionSixSylow hypothesis)
      quotient hsurj hkernel localActor]
    rw [Subgroup.map_commutator, hsetup.localV_image, hlocal,
      Subgroup.map_commutator, hcenter]

public theorem nine_three_mixed_barred_actor_quadratic
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second) :
    letI := sectionSixQuotientAction ctx.hypothesisTwo
    let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let actor := ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a
    let barActor := ((actor.map embedding).subgroupOf P1).map
      (sectionSixQuotientMap ctx.hypothesisTwo)
    commutatorAction barActor (sectionSixLocalV ctx.hypothesisTwo) ≤
      FixedPoints.subgroup barActor (sectionSixLocalV ctx.hypothesisTwo) := by
  let _ := sectionSixQuotientAction ctx.hypothesisTwo
  let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let actor := ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a
  let moduleGroup := sectionSixLocalV ctx.hypothesisTwo
  let inclusion := P1.subtype.comp moduleGroup.subtype
  have hinj : Function.Injective inclusion :=
    P1.subtype_injective.comp moduleGroup.subtype_injective
  have hquad := nine_three_mixed_actor_quadratic ctx hb first second config
  have htransport := nine_three_barred_actor_action_transport ctx actor hquad.1
  apply (Subgroup.map_le_map_iff_of_injective hinj).mp
  rw [htransport.2.1]
  rw [map_inf_centralizer embedding ctx.embedding_injective]
  refine le_inf ?_ ?_
  · have hcenter := nine_two_center_eq_sectionSixV ctx (nine_two_ambient_setup ctx).2.1
    rw [hcenter, ← (sectionSix_barred_action_setup ctx.hypothesisTwo).localV_image,
      show inclusion = P1.subtype.comp moduleGroup.subtype from rfl, ← Subgroup.map_map]
    exact Subgroup.map_mono (Subgroup.map_subtype_le _)
  · rw [htransport.2.2]
    have hcentral := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hquad.2
    have hmapped := Subgroup.map_mono (f := embedding)
      (le_inf (le_refl (⁅ZAt ctx.Γ ctx.criticalPath.a, actor⁆ : Subgroup G)) hcentral)
    rw [map_inf_centralizer embedding ctx.embedding_injective] at hmapped
    exact hmapped.trans inf_le_right

public theorem nine_three_barred_actor_critical_fixed_transport
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (actor : Subgroup G) (hactor : actor ≤ T) :
    letI := sectionSixQuotientAction ctx.hypothesisTwo
    let moduleGroup := sectionSixLocalV ctx.hypothesisTwo
    let barActor := ((actor.map embedding).subgroupOf P1).map
      (sectionSixQuotientMap ctx.hypothesisTwo)
    let inclusion := P1.subtype.comp moduleGroup.subtype
    let fixed := (Subgroup.centralizer
      (sectionSixBarredCriticalPreimage ctx.hypothesisTwo : Set H)).comap embedding
    ((commutatorAction barActor moduleGroup) ⊓
      FixedPoints.subgroup (sectionSixBarredCritical ctx.hypothesisTwo) moduleGroup).map
        inclusion = ((⁅ZAt ctx.Γ ctx.criticalPath.a, actor⁆ : Subgroup G) ⊓ fixed).map
          embedding := by
  let hypothesis := ctx.hypothesisTwo
  let moduleGroup := sectionSixLocalV hypothesis
  let inclusion := P1.subtype.comp moduleGroup.subtype
  let initial := ZAt ctx.Γ ctx.criticalPath.a
  let plane := (⁅initial, actor⁆ : Subgroup G)
  let fixed := (Subgroup.centralizer
    (sectionSixBarredCriticalPreimage hypothesis : Set H)).comap embedding
  let _ := sectionSixQuotientAction hypothesis
  have hsetup := sectionSix_barred_action_setup hypothesis
  have hinj : Function.Injective inclusion :=
    P1.subtype_injective.comp moduleGroup.subtype_injective
  have hmodule : moduleGroup.map P1.subtype = initial.map embedding := by
    rw [hsetup.localV_image,
      nine_two_center_eq_sectionSixV ctx (nine_two_ambient_setup ctx).2.1]
  have hfixedMap : (FixedPoints.subgroup (sectionSixBarredCritical hypothesis)
      moduleGroup).map inclusion = (initial ⊓ fixed).map embedding := by
    apply le_antisymm
    · rintro _ ⟨vector, hvector, rfl⟩
      have hinitial : inclusion vector ∈ initial.map embedding := by
        rw [← hmodule]
        exact Subgroup.mem_map_of_mem P1.subtype vector.property
      obtain ⟨native, hnative, heq⟩ := hinitial
      refine ⟨native, ⟨hnative, ?_⟩, heq⟩
      change embedding native ∈ Subgroup.centralizer
        (sectionSixBarredCriticalPreimage hypothesis : Set H)
      rw [heq]
      exact (hsetup.mem_fixedPoints_iff vector).mp hvector
    · rintro _ ⟨native, hnative, rfl⟩
      have hmoduleMember : embedding native ∈ moduleGroup.map P1.subtype := by
        rw [hmodule]
        exact Subgroup.mem_map_of_mem embedding hnative.1
      obtain ⟨localVector, hlocalVector, heq⟩ := hmoduleMember
      refine ⟨⟨localVector, hlocalVector⟩, ?_, heq⟩
      apply (hsetup.mem_fixedPoints_iff ⟨localVector, hlocalVector⟩).mpr
      change (localVector : H) ∈ Subgroup.centralizer
        (sectionSixBarredCriticalPreimage hypothesis : Set H)
      change (localVector : H) = embedding native at heq
      rw [heq]
      exact hnative.2
  have htransport := nine_three_barred_actor_action_transport ctx actor hactor
  have hplane : plane ≤ initial := by
    apply (Subgroup.map_le_map_iff_of_injective ctx.embedding_injective).mp
    rw [← htransport.2.2, ← hmodule, ← Subgroup.map_map]
    exact Subgroup.map_mono (Subgroup.map_subtype_le _)
  change ((commutatorAction (((actor.map embedding).subgroupOf P1).map
    (sectionSixQuotientMap hypothesis)) moduleGroup) ⊓
      FixedPoints.subgroup (sectionSixBarredCritical hypothesis) moduleGroup).map inclusion =
        (plane ⊓ fixed).map embedding
  rw [Subgroup.map_inf _ _ _ hinj, htransport.2.2, hfixedMap,
    ← Subgroup.map_inf _ _ _ ctx.embedding_injective]
  change (plane ⊓ (initial ⊓ fixed)).map embedding = (plane ⊓ fixed).map embedding
  rw [← inf_assoc, inf_eq_left.mpr hplane]

end Stellmacher.SectionNine
