module
public import Stellmacher.SectionNine.NineTenTerminalClassification
public import Stellmacher.SectionNine.NineNineTerminalIntersectionNormality

/-!
# The same wreath classification on every two-step configuration

The actual terminal order-thirty-two module, wreath core quotient, and
order-eight terminal/preterminal intersection transfer to any two distinct
neighbors of an initial-orbit vertex. Cubic two-arc transitivity moves the
terminal, penultimate, and preterminal vertices simultaneously. The same
conjugation carries both modules, stabilizer, and core, so every cardinality
and the quotient model transfer together. The same map also transports
containment of the middle center, containment in its core, and normalization
by the full middle stabilizer, using the proved terminal intersection geometry.

This is the use of Stellmacher (9.10)(6), printed p.58, at the first and
third vertices and then at the neighbors in (**). It preserves the original
critical path and takes the already-proved terminal packet explicitly; no
new extraction or independently chosen intersection is combined with it.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u w

private theorem quotient_model_map
    {G : Type u} {M : Type w} [Group G] [Group M]
    (equiv : G ≃* G) (K U : Subgroup G)
    (hmodel : QuotientIsModel K U M) :
    QuotientIsModel (K.map equiv.toMonoidHom) (U.map equiv.toMonoidHom) M := by
  obtain ⟨projection, hsurj, hker⟩ := hmodel
  let e := K.equivMapOfInjective equiv.toMonoidHom equiv.injective
  refine ⟨projection.comp e.symm.toMonoidHom, hsurj.comp e.symm.surjective, ?_⟩
  ext x
  change e.symm x ∈ projection.ker ↔ (x:G) ∈ U.map equiv.toMonoidHom
  rw [hker, Subgroup.mem_map_equiv]
  change (e.symm x:G) ∈ U ↔ equiv.symm (x:G) ∈ U
  have heq : (e.symm x:G) = equiv.symm (x:G) := by
    apply equiv.injective
    have hh := congrArg Subtype.val (e.apply_symm_apply x)
    exact hh.trans (equiv.apply_symm_apply (x:G)).symm
  rw [heq]

public theorem nine_ten_two_step_wreath_classification
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^5)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2)
    (hinter : Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) : Subgroup G) = 2^3)
    {left middle right : ctx.Γ.Vertex}
    (hmiddle : IsConjugateVertex ctx.Γ ctx.criticalPath.a middle)
    (hleft : ctx.Γ.adjacent middle left)
    (hright : ctx.Γ.adjacent middle right)
    (hdistinct : left ≠ right) :
    Nat.card (VAt ctx.Γ left) = 2^5 ∧
      QuotientIsModel (GAt ctx.Γ left) (QAt ctx.Γ left) SL2TwoWreathC2 ∧
      Nat.card (VAt ctx.Γ left ⊓ VAt ctx.Γ right : Subgroup G) = 2^3 ∧
      ZAt ctx.Γ middle ≤ VAt ctx.Γ left ⊓ VAt ctx.Γ right ∧
      VAt ctx.Γ left ⊓ VAt ctx.Γ right ≤ QAt ctx.Γ middle ∧
      GAt ctx.Γ middle ≤ Subgroup.normalizer
        ((VAt ctx.Γ left ⊓ VAt ctx.Γ right : Subgroup G) : Set G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let preterminal := cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let penultimate := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hshort : 1 < cp.length := by change 3 < cp.length at hb; omega
  obtain ⟨alignment, halign, _⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  change Γ.act alignment cp.a = penultimate at halign
  obtain ⟨target, htarget⟩ := hmiddle
  have hmiddleOrbit : IsConjugateVertex Γ penultimate middle := by
    refine ⟨alignment⁻¹ * target, ?_⟩
    have hinverse : Γ.act alignment⁻¹ penultimate = cp.a := by
      rw [← halign, ← Γ.act_mul, mul_inv_cancel, Γ.act_one]
    rw [Γ.act_mul, hinverse]
    exact htarget
  have hterminalAdj := nine_five_penultimate_adjacent ctx.toLocalContext
  have hpreAdj := Γ.adjacent_symm (nine_five_previous_adjacent_penultimate
    ctx.toLocalContext hshort preterminal
      ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩)
  have hterminalNe : cp.a' ≠ preterminal :=
    (nine_five_previous_ne_terminal ctx.toLocalContext hshort preterminal
      ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩).symm
  obtain ⟨mover, hmoveLeft, hmoveMiddle, hmoveRight⟩ := nine_seven_two_arc_transport
    ctx.sectionSeven Γ hterminalAdj hpreAdj hterminalNe hleft hright hdistinct
      hmiddleOrbit (lemma_nine_three_ambient ctx hshort middle ⟨target, htarget⟩).1
  change Γ.act mover cp.a' = left at hmoveLeft
  change Γ.act mover penultimate = middle at hmoveMiddle
  let equiv := MulAut.conj mover⁻¹
  have hVleft : (VAt Γ cp.a').map equiv.toMonoidHom = VAt Γ left := by
    rw [← v_act, hmoveLeft]
  have hVright : (VAt Γ preterminal).map equiv.toMonoidHom = VAt Γ right := by
    rw [← v_act, hmoveRight]
  have hGleft : (GAt Γ cp.a').map equiv.toMonoidHom = GAt Γ left := by
    change conjugateBy (stabilizer Γ cp.a') mover⁻¹ = _
    rw [← stabilizer_act, hmoveLeft]
  have hQleft : (QAt Γ cp.a').map equiv.toMonoidHom = QAt Γ left := by
    rw [← q_act, hmoveLeft]
  have hGmiddle : (GAt Γ penultimate).map equiv.toMonoidHom = GAt Γ middle := by
    change conjugateBy (stabilizer Γ penultimate) mover⁻¹ = _
    rw [← stabilizer_act, hmoveMiddle]
  have hQmiddle : (QAt Γ penultimate).map equiv.toMonoidHom = QAt Γ middle := by
    rw [← q_act, hmoveMiddle]
  have hZmiddle : (ZAt Γ penultimate).map equiv.toMonoidHom = ZAt Γ middle := by
    rw [← z_act, hmoveMiddle]
  have hImap : (VAt Γ cp.a' ⊓ VAt Γ preterminal : Subgroup G).map equiv.toMonoidHom =
      VAt Γ left ⊓ VAt Γ right := by
    rw [Subgroup.map_inf _ _ _ equiv.injective, hVleft, hVright]
  have hgeometry := nine_nine_terminal_intersection_core_normalized ctx hshort
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hVleft, Subgroup.card_map_of_injective equiv.injective]
    exact hcard
  · rw [← hGleft, ← hQleft]
    exact quotient_model_map equiv _ _ hmodel
  · rw [← hVleft, ← hVright, ← Subgroup.map_inf _ _ _ equiv.injective,
      Subgroup.card_map_of_injective equiv.injective]
    exact hinter
  · rw [← hZmiddle, ← hImap]
    exact Subgroup.map_mono hgeometry.1
  · rw [← hQmiddle, ← hImap]
    exact Subgroup.map_mono hgeometry.2.1
  · rw [← hGmiddle, ← hImap]
    exact (Subgroup.map_mono hgeometry.2.2).trans (Subgroup.le_normalizer_map equiv.toMonoidHom)

end Stellmacher.SectionNine
