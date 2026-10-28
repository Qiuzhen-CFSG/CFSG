module
public import Stellmacher.SectionNine.NineEightTerminalTransvection
public import Stellmacher.SectionNine.LemmaNineNine
public import Stellmacher.SectionNine.NineNextTransvectionFactor
public import Stellmacher.SectionNine.NineNineTerminalCoreImageSylow
public import Stellmacher.SectionOne.OneSevenLargeTwoGroupDisplacement
public import Theory.GroupAction.SubgroupQuotientCommutatorImage

/-!
# At least sixteen terminal-edge commutators in the wreath case

In the actual order-thirty-two terminal wreath case at critical length greater
than three, the full commutator of the terminal module with its penultimate
edge has order at least sixteen. The action and edge are the literal ones in
the retained context.

Actual (9.9) and (9.8) provide a first-module transvection. The first module
lies in the penultimate core, whose image in the faithful terminal quotient
action is a Sylow two-subgroup of order eight. A canonical support of order
four and its disjoint swapped conjugate give quotient displacement of order
at least eight. The full edge commutator contains the terminal center by the
terminal-core commutator identity; exact quotient counting doubles the bound.

This is the natural wreath edge obstruction used in Stellmacher (9.10)(10)
and (12), printed pp.58–59. Its transport to the second/third edge preserves
the same path and module intersections.
The arbitrary-edge wrapper uses endpoint alignment and local neighbor
transitivity to carry the same commutator bound by one conjugation.
-/
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_terminal_edge_commutator_card_ge_sixteen
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hUcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^5)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2) :
    16 ≤ Nat.card (⁅VAt ctx.Γ ctx.criticalPath.a',
      GAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length-1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ⊓ GAt ctx.Γ ctx.criticalPath.a'⁆ : Subgroup G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let penultimate := cp.path ⟨cp.length-1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let P := GAt Γ cp.a'
  let U := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let edge := GAt Γ penultimate ⊓ P
  let C := ⁅U, edge⁆
  have hshort : 1 < cp.length := by change 3 < cp.length at hb; omega
  have hfirstNot : ¬ ZAt Γ cp.firstStep ≤ U := by
    intro hle
    have hh := lemma_nine_nine_ambient ctx hle
    change 3 < cp.length at hb
    change cp.length ≤ 3 at hh
    omega
  obtain ⟨actor, hactorFirst, _, _, hindex⟩ :=
    nine_eight_terminal_transvection_of_reverse_noncontainment ctx hshort hfirstNot
  obtain ⟨alignment, halign, hterminal⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have horbit : IsConjugateVertex Γ cp.firstStep cp.a' := ⟨alignment, hterminal⟩
  have hdata := nine_next_center_commutator_and_kernel ctx hshort cp.a' horbit
  have hZcard : Nat.card Z = 2 := hdata.1
  have hUcore : ⁅U, QAt Γ cp.a'⁆ = Z := hdata.2.1
  have hQP : QAt Γ cp.a' ≤ P := by
    rw [QAt, CosetGraphContext.q, Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hPU : P ≤ Subgroup.normalizer (U : Set G) := stabilizer_le_normalizer_v Γ cp.a'
  have hZU : Z ≤ U := hUcore ▸
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hQP.trans hPU)
  have hQtEdge : QAt Γ cp.a' ≤ edge := le_inf
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a' penultimate
      (nine_three_initial_extraction_inputs ctx.toLocalContext hshort).1 default).2.2 hQP
  have hZC : Z ≤ C := by
    rw [← hUcore]
    exact Subgroup.commutator_mono le_rfl hQtEdge
  have hCU : C ≤ U := Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((show edge ≤ P from inf_le_right).trans hPU)
  obtain ⟨hN, hW, action, hact, hkernel, _, _, hrank, hyp, hfactor⟩ :=
    nine_next_transvection_factor ctx hshort cp.a' horbit actor hindex
  let _ := hN
  let _ := hW
  let W := U ⧸ Z.subgroupOf U
  let q : U →* W := QuotientGroup.mk' (Z.subgroupOf U)
  let f := action.rangeRestrict
  let induced := f actor
  let factor : Subgroup action.range :=
    ⁅SectionOne.oddCore action.range, Subgroup.zpowers induced⁆ ⊔ Subgroup.zpowers induced
  have hfker : f.ker = pCore 2 P := by rw [MonoidHom.ker_rangeRestrict, hkernel]
  obtain ⟨sylow, hsylow⟩ := nine_nine_terminal_core_image_sylow ctx hshort f
    action.rangeRestrict_surjective hfker
  have hScard : Nat.card sylow = 8 := by
    rw [hsylow]
    exact nine_nine_terminal_core_image_card_eight ctx hshort f
      action.rangeRestrict_surjective hfker hmodel
  have hactorQpen : (actor : G) ∈ QAt Γ penultimate :=
    (nine_three_initial_extraction_inputs ctx.toLocalContext hshort).2.1 hactorFirst
  have haS : induced ∈ (sylow : Subgroup action.range) := by
    rw [hsylow]
    exact Subgroup.mem_map_of_mem f hactorQpen
  have haFactor : induced ∈ factor := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hrank' : Nat.card (commutatorAction (Subgroup.zpowers induced) W) = 2 := by
    rw [← commutatorAction_map_actor_subtype action.range, MonoidHom.map_zpowers]
    exact hrank
  have hWcard : Nat.card W = 16 := by
    have hh := (Z.subgroupOf U).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv, hZcard, hUcard] at hh
    change Nat.card W * 2 = 2^5 at hh
    omega
  have hlarge := SectionOne.oneSevenFactor_large_two_group_commutator_card_ge_eight
    hyp factor (sylow : Subgroup action.range) hfactor sylow.isPGroup' hWcard
      (by rw [hScard]; decide) induced haFactor haS hrank'
  have hQpenEdge : QAt Γ penultimate ≤ edge := le_inf
    (by rw [QAt, CosetGraphContext.q, Γ.twoCoreAt_def]; exact Subgroup.map_subtype_le _)
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core penultimate cp.a'
      ((mem_neighborhood_iff_adjacent Γ).mpr
        (nine_five_penultimate_adjacent ctx.toLocalContext)) default).2.2
  have hSimage : (sylow : Subgroup action.range) ≤ (edge.subgroupOf P).map f := by
    rw [hsylow]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono P hQpenEdge)
  have hdisplacement : commutatorAction (sylow : Subgroup action.range) W ≤
      commutatorAction ((edge.subgroupOf P).map f) W := by
    rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
    apply Subgroup.closure_mono
    rintro point ⟨mover, vector, rfl⟩
    exact ⟨⟨mover, hSimage mover.property⟩, vector, rfl⟩
  have hcommImage : commutatorAction ((edge.subgroupOf P).map f) W =
      (C.subgroupOf U).map q := by
    rw [← commutatorAction_map_actor_subtype action.range, Subgroup.map_map]
    change commutatorAction ((edge.subgroupOf P).map action) W = _
    exact Subgroup.quotient_conjugation_commutatorAction_eq_image P U Z edge
      hPU inf_le_right hN action hact
  have himageLarge : 8 ≤ Nat.card ((C.subgroupOf U).map q) := by
    rw [← hcommImage]
    exact hlarge.trans (Subgroup.card_le_of_le hdisplacement)
  let restriction : C →* W := q.comp (Subgroup.inclusion hCU)
  have hker : restriction.ker = Z.subgroupOf C := by
    ext point
    change q ((Subgroup.inclusion hCU) point) = 1 ↔ (point : G) ∈ Z
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    rfl
  have hrange : restriction.range = (C.subgroupOf U).map q := by
    ext point
    constructor
    · rintro ⟨preimage, rfl⟩
      exact ⟨(Subgroup.inclusion hCU) preimage, preimage.property, rfl⟩
    · rintro ⟨preimage, hpreimage, rfl⟩
      exact ⟨⟨preimage, hpreimage⟩, rfl⟩
  have hcount := restriction.ker.index_mul_card
  rw [Subgroup.index_ker, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv, hZcard, hrange] at hcount
  change 16 ≤ Nat.card C
  omega

/-- Transport the terminal bound to any adjacent edge of the same orbit type. -/
public theorem nine_ten_edge_commutator_card_ge_sixteen
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hUcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^5)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2)
    {middle endpoint : ctx.Γ.Vertex}
    (hmiddle : IsConjugateVertex ctx.Γ ctx.criticalPath.a middle)
    (hadj : ctx.Γ.adjacent middle endpoint) :
    16 ≤ Nat.card (⁅VAt ctx.Γ endpoint, GAt ctx.Γ middle ⊓ GAt ctx.Γ endpoint⁆ : Subgroup G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let penultimate := cp.path ⟨cp.length-1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  obtain ⟨alignment, halign, _⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  change Γ.act alignment cp.a = penultimate at halign
  obtain ⟨target, htarget⟩ := hmiddle
  let initialMover := alignment⁻¹ * target
  have hmiddleMove : Γ.act initialMover penultimate = middle := by
    have hinverse : Γ.act alignment⁻¹ penultimate = cp.a := by
      rw [← halign, ← Γ.act_mul, mul_inv_cancel, Γ.act_one]
    rw [Γ.act_mul, hinverse]
    exact htarget
  have hterminalAdj : Γ.adjacent penultimate cp.a' := nine_five_penultimate_adjacent ctx.toLocalContext
  have hneighbor : Γ.act initialMover cp.a' ∈ neighborhood Γ middle := by
    apply (mem_neighborhood_iff_adjacent Γ).mpr
    simpa only [hmiddleMove] using adjacent_act Γ initialMover hterminalAdj
  obtain ⟨fixer, hfixer⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity
    middle hneighbor ((mem_neighborhood_iff_adjacent Γ).mpr hadj)
  let mover := initialMover * (fixer : G)
  have hmoveMiddle : Γ.act mover penultimate = middle := by
    rw [Γ.act_mul, hmiddleMove]
    exact (Set.ext_iff.mp (Γ.stabilizer_def middle) (fixer : G)).mp fixer.property
  have hmoveEndpoint : Γ.act mover cp.a' = endpoint := by
    rw [Γ.act_mul]
    exact hfixer
  let equiv := MulAut.conj mover⁻¹
  have hVmap : (VAt Γ cp.a').map equiv.toMonoidHom = VAt Γ endpoint := by
    rw [← v_act, hmoveEndpoint]
  have hGmap : (GAt Γ cp.a').map equiv.toMonoidHom = GAt Γ endpoint := by
    change conjugateBy (stabilizer Γ cp.a') mover⁻¹ = _
    rw [← stabilizer_act, hmoveEndpoint]
  have hGmiddleMap : (GAt Γ penultimate).map equiv.toMonoidHom = GAt Γ middle := by
    change conjugateBy (stabilizer Γ penultimate) mover⁻¹ = _
    rw [← stabilizer_act, hmoveMiddle]
  rw [← hVmap, ← hGmap, ← hGmiddleMap, ← Subgroup.map_inf _ _ _ equiv.injective,
    ← Subgroup.map_commutator, Subgroup.card_map_of_injective equiv.injective]
  exact nine_ten_terminal_edge_commutator_card_ge_sixteen ctx hb hUcard hmodel

end Stellmacher.SectionNine
