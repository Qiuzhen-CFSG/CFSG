module
public import Stellmacher.SectionNine.NineNineTerminalClassification
public import Stellmacher.SectionNine.NineFivePreviousCommutation
public import Stellmacher.SectionNine.NineNineTerminalCoreImageSylow
public import Stellmacher.SectionOne.OneSevenInvariantFourDisplacement
public import Stellmacher.SectionOne.OneSevenTwoGroupSupportMove

/-!
# The first center lies in the terminal intersection in (9.9)

Under the original explicit distance-bound and large-intersection inputs,
the first-step center lies in the intersection of the terminal module with
the module two steps before it. This proves the center-containment assertion
following (9.9)(3), without assuming a compatible abstract wreath action.

The actual terminal quotient has order sixteen and the intersection image
has order four. The penultimate core has a two-group image of order eight,
so it carries the canonical transvection support to a complementary support.
This actor preserves the geometric intersection, while the initial-center
transvection fixes it. The invariant-four displacement theorem puts that
transvection's quotient displacement in the intersection image. Its exact
ambient displacement is the first center; pulling back through the unchanged
terminal-center kernel proves the assertion.

Source: Stellmacher (9.9), printed p.56/PDF p.46 of
`refs/files/stellmacher-n-group.pdf`, the sentence after assertion (3).
The final centralizing-conjugator and normalizer-index argument is separate.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem quotient_image_preserved
    {G : Type u} [Group G] [Finite G] (P U Z I : Subgroup G)
    (hPU : P ≤ Subgroup.normalizer (U : Set G))
    (hN : (Z.subgroupOf U).Normal) :
    let _ := hN
    ∀ action : P →* MulAut (U ⧸ Z.subgroupOf U),
      (∀ mover : P, ∀ point : U,
        action mover (QuotientGroup.mk' (Z.subgroupOf U) point) =
          QuotientGroup.mk' (Z.subgroupOf U)
            ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp (hPU mover.property) point).mp point.property⟩) →
      ∀ mover : P, (mover:G) ∈ Subgroup.normalizer (I : Set G) →
        ((I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U))).map
          (action mover).toMonoidHom =
            (I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) := by
  let _ := hN
  dsimp only
  intro action hact mover hnorm
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  apply Subgroup.eq_of_le_of_card_ge
  · rintro point ⟨vector,⟨lift,hlift,rfl⟩,rfl⟩
    change action mover (q lift) ∈ (I.subgroupOf U).map q
    rw [hact]
    exact Subgroup.mem_map_of_mem q
      ((Subgroup.mem_normalizer_iff.mp hnorm (lift:G)).mp hlift)
  · exact (Subgroup.card_map_of_injective (K := (I.subgroupOf U).map q)
      (action mover).injective).symm.le

set_option maxHeartbeats 1000000 in
public theorem nine_nine_first_center_le_terminal_intersection
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
    ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ
        (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let preterminal := cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let penultimate := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let P := GAt Γ cp.a'
  let U := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let R := ZAt Γ cp.firstStep
  let I := U ⊓ VAt Γ preterminal
  have hshort : 1 < cp.length := by change 3 < cp.length at hb; omega
  have hpath : IsCriticalPathOffset Γ cp (cp.length-2) preterminal :=
    ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩
  obtain ⟨hUcard,hmodel,hIcard⟩ := nine_nine_terminal_wreath_classification
    bound ctx hb hcore previous hprevious hne hlarge
  change Nat.card U=2^5 at hUcard
  change Nat.card I=2^3 at hIcard
  have hpreAdj := Γ.adjacent_symm
    (nine_five_previous_adjacent_penultimate ctx.toLocalContext hshort preterminal hpath)
  have htermAdj := nine_five_penultimate_adjacent ctx.toLocalContext
  obtain ⟨alignment,halign,hterminal⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have horbit : IsConjugateVertex Γ cp.firstStep cp.a' := ⟨alignment,hterminal⟩
  have hfour := (lemma_nine_three_ambient ctx hshort cp.a ⟨1,Γ.act_one _⟩).2
  obtain ⟨hZcard,hcomm⟩ := nine_next_center_and_commutator_of_initial_four
    ctx.toLocalContext hfour cp.a' horbit
  change Nat.card Z=2 at hZcard
  have hQP : QAt Γ cp.a' ≤ P := by
    rw [QAt,q,Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hPU : P ≤ Subgroup.normalizer (U : Set G) := stabilizer_le_normalizer_v Γ cp.a'
  have hZU : Z ≤ U := by
    change ⁅U,QAt Γ cp.a'⁆ = Z at hcomm
    rw [← hcomm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hQP.trans hPU)
  have hZpre : Z ≤ VAt Γ preterminal := by
    have hline := (nine_five_penultimate_center_layer_of_initial_four ctx.toLocalContext hfour).1
    exact hline.trans (nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm hpreAdj))
  have hZI : Z ≤ I := le_inf hZU hZpre
  obtain ⟨actor,hactorZa,_,hactorComm,hindex⟩ := nine_nine_initial_transvection ctx hshort hcore
  obtain ⟨hN,hW,action,hact,hkernel,_,_,hrank,hyp,hfactor⟩ :=
    nine_next_transvection_factor ctx hshort cp.a' horbit actor hindex
  let _ := hN
  let _ := hW
  let W := U ⧸ Z.subgroupOf U
  let q : U →* W := QuotientGroup.mk' (Z.subgroupOf U)
  let factor := ⁅SectionOne.oddCore action.range,
    Subgroup.zpowers (action.rangeRestrict actor)⁆ ⊔
      Subgroup.zpowers (action.rangeRestrict actor)
  let J := (I.subgroupOf U).map q
  let Sbar := ((QAt Γ penultimate).subgroupOf P).map action.rangeRestrict
  have hSbarcard : Nat.card Sbar=8 := by
    apply nine_nine_terminal_core_image_card_eight ctx hshort action.rangeRestrict
      action.rangeRestrict_surjective
    · rw [MonoidHom.ker_rangeRestrict,hkernel]
    · exact hmodel
  have hSbarp : IsPGroup 2 Sbar := by
    exact IsPGroup.of_card (p := 2) (n := 3) (by simpa using hSbarcard)
  have hWcard : Nat.card W=16 := by
    have hcount := (Z.subgroupOf U).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv,hZcard,hUcard] at hcount
    change Nat.card W*2=2^5 at hcount
    omega
  have hJcard : Nat.card J=4 := by
    have hcount := (Z.subgroupOf I).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZI).toEquiv,hZcard,hIcard] at hcount
    change Z.relIndex I*2=2^3 at hcount
    have hrel := Subgroup.relIndex_ker (I.subgroupOf U) q
    rw [QuotientGroup.ker_mk',Subgroup.relIndex_subgroupOf (show I≤U from inf_le_left)] at hrel
    change Z.relIndex I=Nat.card J at hrel
    omega
  obtain ⟨conjugator,hmove,hspan⟩ :=
    SectionOne.oneSevenFactor_exists_complementary_two_group_conjugate hyp factor Sbar
      hfactor hSbarp hWcard (by omega)
  obtain ⟨lift,hlift,heq⟩ := conjugator.property
  have hcoreTerm : QAt Γ penultimate ≤ P :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core penultimate cp.a'
      ((mem_neighborhood_iff_adjacent Γ).mpr htermAdj) default).2.2
  have hcorePre : QAt Γ penultimate ≤ GAt Γ preterminal :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core penultimate preterminal
      ((mem_neighborhood_iff_adjacent Γ).mpr hpreAdj) default).2.2
  have hnormI : (lift:G) ∈ Subgroup.normalizer (I : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hPU lift.property,stabilizer_le_normalizer_v Γ preterminal (hcorePre hlift)⟩
  have hJmove : J.map ((conjugator : action.range) : MulAut W).toMonoidHom=J := by
    rw [← heq]
    exact quotient_image_preserved P U Z I hPU hN action hact lift hnormI
  have hactorFirst : (actor:G)∈VAt Γ cp.firstStep :=
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1 hactorZa
  have hcommPre := nine_five_previous_module_commutes_first ctx.toLocalContext hshort
    preterminal hpath
  have haJ : ∀ point∈J, action actor point∈J := by
    rintro point ⟨lift,hlift,rfl⟩
    have hcommute := Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommPre hlift.2)
        (actor:G) hactorFirst
    have hfixed : action actor (q lift)=q lift := by
      rw [hact]
      congr 1
      apply Subtype.ext
      change (actor:G)*(lift:G)*(actor:G)⁻¹=(lift:G)
      change (actor:G)*(lift:G)=(lift:G)*(actor:G) at hcommute
      rw [hcommute,mul_inv_cancel_right]
    rw [hfixed]
    exact Subgroup.mem_map_of_mem q hlift
  have hactorFactor : action.rangeRestrict actor∈factor :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hline := SectionOne.oneSevenFactor_displacement_le_invariant_four
    action.range hyp factor hfactor (action.rangeRestrict actor) (conjugator:action.range)
      hactorFactor hrank hmove hspan J hJcard haJ hJmove
  change commutatorAction (Subgroup.zpowers (action actor)) W ≤ J at hline
  have hactorNative : (Subgroup.zpowers (actor:G)).subgroupOf P=Subgroup.zpowers actor := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr actor.property),MonoidHom.map_zpowers]
    rfl
  have hlineImage := Subgroup.quotient_conjugation_commutatorAction_eq_image
    P U Z (Subgroup.zpowers (actor:G)) hPU (Subgroup.zpowers_le.mpr actor.property)
      hN action hact
  rw [hactorNative,MonoidHom.map_zpowers,hactorComm] at hlineImage
  rw [hlineImage] at hline
  have hRU : R≤U := by
    change ⁅U,Subgroup.zpowers (actor:G)⁆=R at hactorComm
    rw [← hactorComm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((Subgroup.zpowers_le.mpr actor.property).trans hPU)
  intro point hpoint
  have hmem : q ⟨point,hRU hpoint⟩ ∈ J := hline (Subgroup.mem_map_of_mem q hpoint)
  have hpreimage : (⟨point,hRU hpoint⟩ : U) ∈ ((I.subgroupOf U).map q).comap q := hmem
  rw [Subgroup.comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr
    (Subgroup.subgroupOf_mono U hZI)] at hpreimage
  exact hpreimage

end Stellmacher.SectionNine
