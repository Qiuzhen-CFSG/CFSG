module
public import Stellmacher.SectionNine.NineNinePreviousClassification
public import Stellmacher.SectionNine.NineFivePenultimateResidualGeneration

/-!
# Transport the (9.9)(3) classification to the terminal two-arc

The preceding module's order-thirty-two wreath classification transports to
the terminal module, and its order-eight intersection transports to the
terminal/preterminal module intersection. The cubic two-arc transitivity at
the initial-orbit middle vertices supplies one actor carrying both neighboring
vertices simultaneously. Subgroup maps therefore preserve the actual
intersection, while composing the quotient map with the conjugation
equivalence preserves the stated kernel.

This is the classification transport immediately after assertion (3) in
Stellmacher (9.9), printed p.56/PDF p.46 of
`refs/files/stellmacher-n-group.pdf`. It does not assert that the first-step
center lies in that intersection or produce the later centralizing conjugator;
those require further local-action geometry.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u w

private theorem quotient_model_map
    {G : Type u} {M : Type w} [Group G] [Group M]
    (equiv : G ≃* G) (K U : Subgroup G)
    (hmodel : QuotientIsModel K U M) :
    QuotientIsModel (K.map equiv.toMonoidHom) (U.map equiv.toMonoidHom) M := by
  obtain ⟨projection,hsurj,hker⟩ := hmodel
  let e := K.equivMapOfInjective equiv.toMonoidHom equiv.injective
  refine ⟨projection.comp e.symm.toMonoidHom,hsurj.comp e.symm.surjective,?_⟩
  ext x
  change e.symm x ∈ projection.ker ↔ (x:G) ∈ U.map equiv.toMonoidHom
  rw [hker,Subgroup.mem_map_equiv]
  change (e.symm x:G) ∈ U ↔ equiv.symm (x:G) ∈ U
  have heq : (e.symm x:G) = equiv.symm (x:G) := by
    apply equiv.injective
    have hh := congrArg Subtype.val (e.apply_symm_apply x)
    exact hh.trans (equiv.apply_symm_apply (x:G)).symm
  rw [heq]

public theorem nine_nine_terminal_wreath_classification
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (bound : ∀ shifted : AmbientSectionNineContext H S0 S P1 P2 embedding T A B,
      ZAt shifted.Γ shifted.criticalPath.a' ≤
        VAt shifted.Γ shifted.criticalPath.firstStep → shifted.criticalPath.length ≤ 3)
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hcore : VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : previous ≠ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card (VAt ctx.Γ previous ⊓
      VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) ≤ Nat.card (VAt ctx.Γ previous)) :
    let preterminal := ctx.criticalPath.path ⟨ctx.criticalPath.length - 2,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^5 ∧
      QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a') (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2 ∧
      Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ preterminal : Subgroup G) = 2^3 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let preterminal := cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let penultimate := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hshort : 1 < cp.length := by change 3 < cp.length at hb; omega
  obtain ⟨hcard,hmodel,hinter⟩ := nine_nine_previous_wreath_classification bound ctx hb hcore
    previous hprevious hne hlarge
  obtain ⟨alignment,halign,_⟩ := lemma_seven_five_endpoint_alignment ctx.sectionSeven Γ cp ctx.commutator_eq
  have hpenOrbit : IsConjugateVertex Γ cp.a penultimate := ⟨alignment,halign⟩
  have hterminalAdj := nine_five_penultimate_adjacent ctx.toLocalContext
  have hpreAdj := Γ.adjacent_symm (nine_five_previous_adjacent_penultimate
    ctx.toLocalContext hshort preterminal
      ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩)
  have hdistinct : cp.a' ≠ preterminal :=
    (nine_five_previous_ne_terminal ctx.toLocalContext hshort preterminal
      ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩).symm
  have hpenModel := (lemma_nine_three_ambient ctx hshort penultimate hpenOrbit).1
  obtain ⟨mover,hmovePrevious,_,hmoveFirst⟩ := nine_seven_two_arc_transport ctx.sectionSeven Γ
    ((mem_neighborhood_iff_adjacent Γ).mp hprevious) cp.firstStep_adj hne
    hterminalAdj hpreAdj hdistinct hpenOrbit hpenModel
  change Γ.act mover previous = cp.a' at hmovePrevious
  let equiv := MulAut.conj mover⁻¹
  have hVprevious : (VAt Γ previous).map equiv.toMonoidHom = VAt Γ cp.a' := by
    rw [← v_act, hmovePrevious]
  have hVfirst : (VAt Γ cp.firstStep).map equiv.toMonoidHom = VAt Γ preterminal := by
    rw [← v_act, hmoveFirst]
  have hGprevious : (GAt Γ previous).map equiv.toMonoidHom = GAt Γ cp.a' := by
    change conjugateBy (stabilizer Γ previous) mover⁻¹ = _
    rw [← stabilizer_act,hmovePrevious]
  have hQprevious : (QAt Γ previous).map equiv.toMonoidHom = QAt Γ cp.a' := by
    rw [← q_act,hmovePrevious]
  refine ⟨?_,?_,?_⟩
  · change Nat.card (VAt Γ cp.a')=2^5
    rw [← hVprevious,Subgroup.card_map_of_injective equiv.injective]
    exact hcard
  · change QuotientIsModel (GAt Γ cp.a') (QAt Γ cp.a') SL2TwoWreathC2
    rw [← hGprevious,← hQprevious]
    exact quotient_model_map equiv _ _ hmodel
  · change Nat.card (VAt Γ cp.a' ⊓ VAt Γ preterminal : Subgroup G)=2^3
    rw [← hVprevious,← hVfirst,← Subgroup.map_inf _ _ _ equiv.injective,
      Subgroup.card_map_of_injective equiv.injective]
    exact hinter

end Stellmacher.SectionNine
