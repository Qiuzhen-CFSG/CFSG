module

public import Stellmacher.SectionOne.OneSevenSylowHyperplaneKernel
public import Stellmacher.SectionNine.NineThreeFinalCoreHyperplaneSetup
public import Stellmacher.SectionNine.NineTwoCenterSectionSixModule

/-!
# Faithfulness on the actual rank-three core intersection in (9.3)

Transport the canonical invariant-hyperplane kernel theorem to every Sylow
of the same actor group, and then through an injective vector map compatible
with a quotient conjugation action. In the original ambient Section Nine
context, this proves that any Sylow-invariant order-eight subgroup of the
initial center has the same local pointwise centralizer as the whole center.

For the actual mixed centralizer C, put D = O2(C). The supplied geometric
conjugator gives an ambient Sylow normalizing the actual Za intersection D.
In the order-eight case, its centralizer inside D is exactly C_D(Za).
The quotient remains the named Section Six action and the vector map is
the actual composition of subgroup inclusions into the original H.

This is an action-kernel transport, not the outstanding odd-layer
containment. In particular it does not assert that the odd layer normalizes
Za intersection D. Source: Stellmacher (9.3), printed p.50/PDF p.40 of
`refs/files/stellmacher-n-group.pdf`, full final R0,C0 paragraph.
-/

open scoped Pointwise

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem fixing_kernel_eq_bot_of_invariant_conjugate_sylow
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [MulDistribMulAction K V]
    (sylow : Sylow 2 K)
    (hkernel : ∀ hyperplane : Subgroup V, IsInvariant sylow V hyperplane →
      Nat.card hyperplane = 8 → fixingSubgroup K (hyperplane : Set V) = ⊥)
    (other : Sylow 2 K) (hyperplane : Subgroup V)
    (hinvariant : IsInvariant other V hyperplane) (hcard : Nat.card hyperplane = 8) :
    fixingSubgroup K (hyperplane : Set V) = ⊥ := by
  obtain ⟨actor, hactor⟩ := MulAction.exists_smul_eq K other sylow
  let transported := hyperplane.map
    (MulDistribMulAction.toMulAut K V actor).toMonoidHom
  have htransported : IsInvariant sylow V transported := by
    constructor
    intro member vector
    have hmember : (member : K) ∈ (other : Subgroup K).map
        (MulAut.conj actor).toMonoidHom := by
      change (member : K) ∈ (actor • other : Sylow 2 K)
      rw [hactor]
      exact member.property
    obtain ⟨preimage, hpreimage, heq⟩ := hmember
    have hforward : ∀ vector : V, vector ∈ transported → member • vector ∈ transported := by
      rintro vector ⟨original, horiginal, rfl⟩
      refine ⟨preimage • original,
        (hinvariant.invariant ⟨preimage, hpreimage⟩ original).mp horiginal, ?_⟩
      change actor • (preimage • original) = (member : K) • (actor • original)
      rw [← heq]
      simp [MulAut.conj_apply, mul_smul]
    constructor
    · exact hforward vector
    · intro hvector
      have hinv : (member⁻¹ : sylow) • ((member : sylow) • vector) ∈ transported := by
        obtain ⟨original, horiginal, heqOriginal⟩ := hvector
        refine ⟨preimage⁻¹ • original,
          (hinvariant.invariant (⟨preimage, hpreimage⟩ : other)⁻¹ original).mp horiginal, ?_⟩
        change actor • (preimage⁻¹ • original) = (member : K)⁻¹ • ((member : K) • vector)
        change actor • original = (member : K) • vector at heqOriginal
        rw [← heqOriginal]
        rw [← heq]
        simp [MulAut.conj_apply, mul_smul]
      simpa using hinv
  have htransportedCard : Nat.card transported = 8 := by
    change Nat.card (hyperplane.map
      (MulDistribMulAction.toMulAut K V actor).toMonoidHom) = 8
    rw [Subgroup.card_map_of_injective
      (f := (MulDistribMulAction.toMulAut K V actor).toMonoidHom)
      (MulDistribMulAction.toMulAut K V actor).injective]
    exact hcard
  have hbot := hkernel transported htransported htransportedCard
  apply le_bot_iff.mp
  intro element helement
  have hconj : MulAut.conj actor element ∈ fixingSubgroup K (transported : Set V) := by
    rw [mem_fixingSubgroup_iff] at helement ⊢
    rintro vector ⟨original, horiginal, rfl⟩
    change (actor * element * actor⁻¹) • (actor • original) = actor • original
    simp [mul_smul, helement original horiginal]
  rw [hbot] at hconj
  exact (MulAut.conj actor).injective (by simpa using hconj)

public theorem centralizer_le_of_quotient_hyperplane_kernel
    {K X V H : Type u} [Group K] [Group X] [Group V] [Group H]
    [Finite V] [Finite H] [MulDistribMulAction X V]
    (quotient : K →* X) (actorMap : K →* H) (vectorMap : V →* H)
    (hinjective : Function.Injective vectorMap)
    (hcompatible : ∀ actor : K, ∀ vector : V,
      vectorMap (quotient actor • vector) =
        actorMap actor * vectorMap vector * (actorMap actor)⁻¹)
    (sylow : Subgroup K) (hyperplane : Subgroup H)
    (hle : hyperplane ≤ vectorMap.range)
    (hnormal : sylow.map actorMap ≤ Subgroup.normalizer (hyperplane : Set H))
    (hcard : Nat.card hyperplane = 8)
    (hkernel : ∀ plane : Subgroup V, IsInvariant (sylow.map quotient) V plane →
      Nat.card plane = 8 → fixingSubgroup X (plane : Set V) = ⊥) :
    actorMap.range ⊓ Subgroup.centralizer (hyperplane : Set H) ≤
      Subgroup.centralizer (vectorMap.range : Set H) := by
  let plane := hyperplane.comap vectorMap
  have hplane : plane.map vectorMap = hyperplane := Subgroup.map_comap_eq_self hle
  have hplaneCard : Nat.card plane = 8 := by
    calc
      Nat.card plane = Nat.card (plane.map vectorMap) :=
        Nat.card_congr (plane.equivMapOfInjective vectorMap hinjective).toEquiv
      _ = 8 := by rw [hplane, hcard]
  have hinvariant : IsInvariant (sylow.map quotient) V plane := by
    constructor
    intro actor vector
    obtain ⟨original, horiginal, heq⟩ := actor.property
    have hnorm := hnormal (Subgroup.mem_map_of_mem actorMap horiginal)
    change vectorMap vector ∈ hyperplane ↔ vectorMap ((actor : X) • vector) ∈ hyperplane
    rw [← heq, hcompatible]
    exact Subgroup.mem_normalizer_iff.mp hnorm (vectorMap vector)
  have hbot := hkernel plane hinvariant hplaneCard
  rintro element ⟨⟨actor, rfl⟩, hcentral⟩
  have hfix : quotient actor ∈ fixingSubgroup X (plane : Set V) := by
    rw [mem_fixingSubgroup_iff]
    intro vector hvector
    apply hinjective
    rw [hcompatible]
    rw [← Subgroup.mem_centralizer_iff.mp hcentral (vectorMap vector) hvector]
    simp [mul_assoc]
  have hidentity : quotient actor = 1 := by simpa [hbot] using hfix
  rw [Subgroup.mem_centralizer_iff]
  rintro vector ⟨original, rfl⟩
  have hfixed := hcompatible actor original
  rw [hidentity, one_smul] at hfixed
  exact (mul_inv_eq_iff_eq_mul.mp hfixed.symm).symm

public theorem nine_three_sylow_invariant_hyperplane_local_centralizer
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (rank : NineThreeNativeActionRankData ctx)
    (hyperplane : Subgroup H)
    (hle : hyperplane ≤ (ZAt ctx.Γ ctx.criticalPath.a).map embedding)
    (hcard : Nat.card hyperplane = 8)
    (sylow : Sylow 2 H) (hsylow : (sylow : Subgroup H) ≤ P1)
    (hnormal : (sylow : Subgroup H) ≤ Subgroup.normalizer (hyperplane : Set H)) :
    P1 ⊓ Subgroup.centralizer (hyperplane : Set H) ≤
      Subgroup.centralizer ((ZAt ctx.Γ ctx.criticalPath.a).map embedding : Set H) := by
  let _ := rank.elementary
  let _ := sectionSixQuotientAction ctx.hypothesisTwo
  let vectors := sectionSixLocalV ctx.hypothesisTwo
  let quotient := sectionSixQuotientMap ctx.hypothesisTwo
  let vectorMap : vectors →* H := P1.subtype.comp vectors.subtype
  let localSylow := sylow.subtype hsylow
  have hrange : vectorMap.range = (ZAt ctx.Γ ctx.criticalPath.a).map embedding := by
    change (P1.subtype.comp vectors.subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [(sectionSix_barred_action_setup ctx.hypothesisTwo).localV_image,
      nine_two_center_eq_sectionSixV ctx (nine_two_ambient_setup ctx).2.1]
  have hcompatible (actor : P1) (vector : vectors) :
      vectorMap (quotient actor • vector) =
        (actor : H) * vectorMap vector * (actor : H)⁻¹ := by
    exact congrArg P1.subtype
      (SectionTwo.quotientConjugationAction_smul_coe
        (sectionSixSylow ctx.hypothesisTwo) quotient
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) actor vector)
  have hnormalLocal : (localSylow : Subgroup P1).map P1.subtype ≤
      Subgroup.normalizer (hyperplane : Set H) := by
    rintro member ⟨original, horiginal, rfl⟩
    exact hnormal horiginal
  have hkernel (plane : Subgroup vectors)
      (hinvariant : IsInvariant ((localSylow : Subgroup P1).map quotient) vectors plane)
      (hplaneCard : Nat.card plane = 8) :
      fixingSubgroup (SectionSixBarP1 ctx.hypothesisTwo) (plane : Set vectors) = ⊥ := by
    apply fixing_kernel_eq_bot_of_invariant_conjugate_sylow
      (sectionSixBarSylow ctx.hypothesisTwo) ?_
      (localSylow.mapSurjective (QuotientGroup.mk'_surjective _)) plane hinvariant hplaneCard
    intro original hinvariantOriginal hcardOriginal
    exact SectionOne.oneSeven_sylow_invariant_hyperplane_fixing_eq_bot
      rank.action_hypotheses (sectionSixBarSylow ctx.hypothesisTwo)
      rank.generated rank.unique_maximal rank.fixed_product_eq_bot rank.factor_count
      original hinvariantOriginal hcardOriginal
  have hbound := centralizer_le_of_quotient_hyperplane_kernel
    quotient P1.subtype vectorMap (P1.subtype_injective.comp vectors.subtype_injective)
    hcompatible (localSylow : Subgroup P1) hyperplane (by rwa [hrange])
    hnormalLocal hcard hkernel
  simpa only [Subgroup.range_subtype, hrange] using hbound

public theorem nine_three_final_core_intersection_centralizer_eq
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
    (hgeometry :
      let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
      let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
        ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
      Nat.card mixed = 2 ∧ ∃ conjugator : G,
        conjugator ∈ GAt ctx.Γ ctx.criticalPath.a ∧
        T.map (MulAut.conj conjugator).toMonoidHom ≤
          Subgroup.centralizer (mixed : Set G)) :
    let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
      ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
    let centralizer := Subgroup.centralizer (mixed.map embedding : Set H)
    let core := (pCore 2 centralizer).map centralizer.subtype
    let vectors := (ZAt ctx.Γ ctx.criticalPath.a).map embedding
    Nat.card (vectors ⊓ core : Subgroup H) = 8 →
      core ⊓ Subgroup.centralizer (vectors ⊓ core : Set H) =
        core ⊓ Subgroup.centralizer (vectors : Set H) := by
  let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
    ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
  let centralizer := Subgroup.centralizer (mixed.map embedding : Set H)
  let core := (pCore 2 centralizer).map centralizer.subtype
  let vectors := (ZAt ctx.Γ ctx.criticalPath.a).map embedding
  change Nat.card (vectors ⊓ core : Subgroup H) = 8 →
    core ⊓ Subgroup.centralizer (vectors ⊓ core : Set H) =
      core ⊓ Subgroup.centralizer (vectors : Set H)
  intro hcard
  obtain ⟨sylow, hsylow, hnormal⟩ := nine_three_final_core_intersection_sylow_normalized
    ctx hb hlarge first second config hgeometry
  have hgroup := (nine_two_ambient_setup ctx).2.1
  have hcore : core ≤ P1 := by
    rw [← hgroup]
    exact (nine_three_final_centralizer_setup_of_mixed_sylow
      ctx first second config hgeometry).2.2
  have hsylowP1 : (sylow : Subgroup H) ≤ P1 := by
    rw [← hgroup]
    exact hsylow.trans inf_le_right
  have hcentral := nine_three_sylow_invariant_hyperplane_local_centralizer
    ctx rank (vectors ⊓ core) inf_le_left hcard sylow hsylowP1 hnormal
  apply le_antisymm
  · exact le_inf inf_le_left ((inf_le_inf hcore le_rfl).trans hcentral)
  · exact inf_le_inf_left core (Subgroup.centralizer_le inf_le_left)

end Stellmacher.SectionNine
