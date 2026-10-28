module

public import Stellmacher.SectionOne.OneSevenSylowHyperplaneStabilizer
public import Stellmacher.SectionNine.NineThreeFinalCoreHyperplaneKernel

/-!
# The actual rank-three intersection's local normalizer

Transport the canonical setwise hyperplane stabilizer to any Sylow of
the same actor group, and then through the actual quotient conjugation
action and original embedding. The local normalizer is the join of the
selected Sylow and the full-center centralizer. The latter kernel is
retained explicitly; it is not assumed to be a two-group.

For the prescribed mixed centralizer C, its intersection with P₁ already
normalizes the core intersection. Conversely the selected Sylow and the
full-center centralizer lie in C. In the order-eight case this gives
N_{P₁}(Za ∩ O₂(C)) = C ∩ P₁.

This controls actors in P₁ only. It does not assume or prove that the
whole odd layer of C normalizes the intersection or lies in P₁.
The outstanding odd-layer commutator containment is a separate step.
Source: Stellmacher (9.3), printed p.50/PDF p.40 of
`refs/files/stellmacher-n-group.pdf`, full final R₀,C₀ paragraph.
-/

open scoped Pointwise

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem setwise_stabilizer_le_of_invariant_conjugate_sylow
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [MulDistribMulAction K V]
    (sylow : Sylow 2 K)
    (hstabilizer : ∀ hyperplane : Subgroup V, IsInvariant sylow V hyperplane →
      Nat.card hyperplane = 8 → ∀ element : K,
      (∀ vector : V, vector ∈ hyperplane ↔ element • vector ∈ hyperplane) →
        element ∈ (sylow : Subgroup K))
    (other : Sylow 2 K) (hyperplane : Subgroup V)
    (hinvariant : IsInvariant other V hyperplane) (hcard : Nat.card hyperplane = 8)
    (element : K)
    (hsetwise : ∀ vector : V, vector ∈ hyperplane ↔ element • vector ∈ hyperplane) :
    element ∈ (other : Subgroup K) := by
  obtain ⟨actor, hactor⟩ := MulAction.exists_smul_eq K other sylow
  let transported := hyperplane.map
    (MulDistribMulAction.toMulAut K V actor).toMonoidHom
  have hmem (vector : V) : vector ∈ transported ↔ actor⁻¹ • vector ∈ hyperplane := by
    constructor
    · rintro ⟨original, horiginal, rfl⟩
      simpa using horiginal
    · intro hvector
      exact ⟨actor⁻¹ • vector, hvector, by simp⟩
  have htransported : IsInvariant sylow V transported := by
    constructor
    intro member vector
    have hmember : (member : K) ∈ (other : Subgroup K).map
        (MulAut.conj actor).toMonoidHom := by
      change (member : K) ∈ (actor • other : Sylow 2 K)
      rw [hactor]
      exact member.property
    obtain ⟨preimage, hpreimage, heq⟩ := hmember
    rw [hmem, hmem]
    change actor⁻¹ • vector ∈ hyperplane ↔
      actor⁻¹ • ((member : K) • vector) ∈ hyperplane
    have hsmul : actor⁻¹ • ((member : K) • vector) =
        preimage • (actor⁻¹ • vector) := by
      rw [← heq]
      simp [MulAut.conj_apply, mul_smul]
    rw [hsmul]
    exact hinvariant.invariant ⟨preimage, hpreimage⟩ _
  have htransportedCard : Nat.card transported = 8 := by
    change Nat.card (hyperplane.map
      (MulDistribMulAction.toMulAut K V actor).toMonoidHom) = 8
    rw [Subgroup.card_map_of_injective
      (f := (MulDistribMulAction.toMulAut K V actor).toMonoidHom)
      (MulDistribMulAction.toMulAut K V actor).injective]
    exact hcard
  have hconjSetwise (vector : V) : vector ∈ transported ↔
      MulAut.conj actor element • vector ∈ transported := by
    rw [hmem, hmem]
    simpa [MulAut.conj_apply, mul_smul] using hsetwise (actor⁻¹ • vector)
  have hconj := hstabilizer transported htransported htransportedCard
    (MulAut.conj actor element) hconjSetwise
  have hmap : MulAut.conj actor element ∈
      (other : Subgroup K).map (MulAut.conj actor).toMonoidHom := by
    change MulAut.conj actor element ∈ (actor • other : Sylow 2 K)
    rwa [hactor]
  obtain ⟨original, horiginal, heq⟩ := hmap
  exact (MulAut.conj actor).injective heq ▸ horiginal

public theorem normalizer_le_of_quotient_hyperplane_stabilizer
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
    (hstabilizer : ∀ plane : Subgroup V, IsInvariant (sylow.map quotient) V plane →
      Nat.card plane = 8 → ∀ element : X,
      (∀ vector : V, vector ∈ plane ↔ element • vector ∈ plane) →
        element ∈ sylow.map quotient) :
    actorMap.range ⊓ Subgroup.normalizer (hyperplane : Set H) ≤
      sylow.map actorMap ⊔
        (actorMap.range ⊓ Subgroup.centralizer (vectorMap.range : Set H)) := by
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
  rintro element ⟨⟨actor, rfl⟩, hnorm⟩
  have hsetwise (vector : V) : vector ∈ plane ↔ quotient actor • vector ∈ plane := by
    change vectorMap vector ∈ hyperplane ↔ vectorMap (quotient actor • vector) ∈ hyperplane
    rw [hcompatible]
    exact Subgroup.mem_normalizer_iff.mp hnorm (vectorMap vector)
  obtain ⟨original, horiginal, heq⟩ :=
    hstabilizer plane hinvariant hplaneCard (quotient actor) hsetwise
  let kernelActor := original⁻¹ * actor
  have hkernel : quotient kernelActor = 1 := by simp [kernelActor, heq]
  have hcentral : actorMap kernelActor ∈ Subgroup.centralizer (vectorMap.range : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro vector ⟨preimage, rfl⟩
    have hfixed := hcompatible kernelActor preimage
    rw [hkernel, one_smul] at hfixed
    exact (mul_inv_eq_iff_eq_mul.mp hfixed.symm).symm
  have hproduct : actorMap actor = actorMap original * actorMap kernelActor := by
    simp [kernelActor]
  rw [hproduct]
  apply Subgroup.mul_mem
  · exact (show sylow.map actorMap ≤ _ from le_sup_left)
      (Subgroup.mem_map_of_mem actorMap horiginal)
  · exact (show actorMap.range ⊓ Subgroup.centralizer (vectorMap.range : Set H) ≤ _
      from le_sup_right) ⟨⟨kernelActor, rfl⟩, hcentral⟩

public theorem nine_three_sylow_invariant_hyperplane_local_normalizer
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
    P1 ⊓ Subgroup.normalizer (hyperplane : Set H) =
      (sylow : Subgroup H) ⊔
        (P1 ⊓ Subgroup.centralizer ((ZAt ctx.Γ ctx.criticalPath.a).map embedding : Set H)) := by
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
  have hsylowMap : (localSylow : Subgroup P1).map P1.subtype = (sylow : Subgroup H) :=
    Subgroup.map_subgroupOf_eq_of_le hsylow
  have hstabilizer (plane : Subgroup vectors)
      (hinvariant : IsInvariant ((localSylow : Subgroup P1).map quotient) vectors plane)
      (hplaneCard : Nat.card plane = 8) (element : SectionSixBarP1 ctx.hypothesisTwo)
      (hsetwise : ∀ vector : vectors, vector ∈ plane ↔ element • vector ∈ plane) :
      element ∈ (localSylow : Subgroup P1).map quotient := by
    apply setwise_stabilizer_le_of_invariant_conjugate_sylow
      (sectionSixBarSylow ctx.hypothesisTwo) ?_
      (localSylow.mapSurjective (QuotientGroup.mk'_surjective _))
      plane hinvariant hplaneCard element hsetwise
    intro original hinvariantOriginal hcardOriginal actor hactor
    exact SectionOne.oneSeven_sylow_invariant_hyperplane_stabilizer_le_sylow
      rank.action_hypotheses (sectionSixBarSylow ctx.hypothesisTwo)
      rank.generated rank.unique_maximal rank.fixed_product_eq_bot rank.factor_count
      original hinvariantOriginal hcardOriginal actor hactor
  apply le_antisymm
  · have hbound := normalizer_le_of_quotient_hyperplane_stabilizer
      quotient P1.subtype vectorMap (P1.subtype_injective.comp vectors.subtype_injective)
      hcompatible (localSylow : Subgroup P1) hyperplane (by rwa [hrange])
      (by rwa [hsylowMap]) hcard hstabilizer
    simpa only [Subgroup.range_subtype, hrange, hsylowMap] using hbound
  · refine sup_le (le_inf hsylow hnormal) (le_inf inf_le_left ?_)
    exact inf_le_right.trans
      ((Subgroup.centralizer_le hle).trans (Subgroup.centralizer_le_normalizer _))

public theorem nine_three_final_core_intersection_local_normalizer_eq
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
      P1 ⊓ Subgroup.normalizer (vectors ⊓ core : Set H) = centralizer ⊓ P1 := by
  let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
    ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
  let centralizer := Subgroup.centralizer (mixed.map embedding : Set H)
  let core := (pCore 2 centralizer).map centralizer.subtype
  let vectors := (ZAt ctx.Γ ctx.criticalPath.a).map embedding
  change Nat.card (vectors ⊓ core : Subgroup H) = 8 → _
  intro hcard
  obtain ⟨sylow, hsylow, hnormal⟩ := nine_three_final_core_intersection_sylow_normalized
    ctx hb hlarge first second config hgeometry
  have hlocal : (GAt ctx.Γ ctx.criticalPath.a).map embedding = P1 :=
    (nine_two_ambient_setup ctx).2.1
  rw [hlocal] at hsylow
  have heq := nine_three_sylow_invariant_hyperplane_local_normalizer
    ctx rank (vectors ⊓ core) inf_le_left hcard sylow
    (hsylow.trans inf_le_right) hnormal
  change P1 ⊓ Subgroup.normalizer (vectors ⊓ core : Set H) =
    (sylow : Subgroup H) ⊔ (P1 ⊓ Subgroup.centralizer (vectors : Set H)) at heq
  change P1 ⊓ Subgroup.normalizer (vectors ⊓ core : Set H) = centralizer ⊓ P1
  rw [heq]
  have hmixed : mixed.map embedding ≤ vectors :=
    Subgroup.map_mono (nine_three_normalized_pair_centralizer
      ctx hb hlarge first second config).1
  apply le_antisymm
  · exact sup_le hsylow
      (le_inf (inf_le_right.trans (Subgroup.centralizer_le hmixed)) inf_le_left)
  · have hnormalizer := (nine_three_final_core_intersection_normalizer_and_commutator
      ctx hb hlarge first second config hgeometry).1
    rw [hlocal] at hnormalizer
    rw [← heq]
    exact le_inf inf_le_right hnormalizer


end Stellmacher.SectionNine
