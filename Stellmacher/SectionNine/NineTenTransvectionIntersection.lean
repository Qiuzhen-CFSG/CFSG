module
public import Stellmacher.SectionNine.NineFivePreviousCommutation
public import Stellmacher.SectionNine.NineFiveConjugatorAlgebra
public import Stellmacher.SectionNine.NineSevenNormalityObstructions
public import Stellmacher.SectionNine.NineNineTerminalCoreImageSylow
public import Stellmacher.SectionNine.NineFourCentralActionRecognition
public import Stellmacher.SectionNine.NineNextTransvectionFactor
public import Stellmacher.SectionOne.OneSevenInvariantFourDisplacement
public import Stellmacher.SectionOne.OneSevenTwoGroupSupportMove

/-!
# A retained transvection displacement lies in the backward intersection

Suppose the actual terminal module has order thirty-two, its core quotient
is the wreath product SL₂(2) ≀ C₂, and the terminal/preterminal intersection
has order eight. For any supplied actor in the first module inducing a
transvection on the terminal module modulo its center, the actor's full
cyclic commutator lies in that intersection and escapes the middle center. The actor is retained and need
not belong to the initial center.

Use the literal quotient conjugation action and its canonical transvection
factor. The penultimate-core image is the actual Sylow two-subgroup of order
eight, so it moves the four-element factor support to a complementary support.
It preserves the four-element geometric intersection image, and the supplied
actor fixes that image by the backward-module commutation theorem. The
invariant-four displacement theorem therefore places the displacement in the
intersection image. Lifting through the unchanged terminal-center kernel
proves the full ambient containment. If the displacement lay in the middle
center, the same core actor would fix its nontrivial quotient line while
exchanging its support with a disjoint support, a contradiction.

This generalizes the invariant-four calculation following Stellmacher
(9.9)(3), printed p.56, for the retained-actor step before (9.10)(7), printed
p.58 of `refs/files/stellmacher-n-group.pdf`. It makes no identification of
the cyclic displacement with the full initial-center commutator.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

set_option maxHeartbeats 1000000 in
public theorem nine_ten_transvection_displacement_intersection_geometry
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hUcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^5)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2)
    (hIcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) : Subgroup G) = 2^3)
    (actor : GAt ctx.Γ ctx.criticalPath.a')
    (hactorFirst : (actor:G) ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a',Subgroup.zpowers (actor:G)⁆ ⊔ ZAt ctx.Γ ctx.criticalPath.a')
      (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    ⁅VAt ctx.Γ ctx.criticalPath.a',Subgroup.zpowers (actor:G)⁆ ≤
      VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ
        (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ∧
      ¬ ⁅VAt ctx.Γ ctx.criticalPath.a',Subgroup.zpowers (actor:G)⁆ ≤ ZAt ctx.Γ
        (ctx.criticalPath.path ⟨ctx.criticalPath.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let preterminal := cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let penultimate := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let P := GAt Γ cp.a'
  let U := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let R := ⁅U,Subgroup.zpowers (actor:G)⁆
  let I := U ⊓ VAt Γ preterminal
  have hshort : 1 < cp.length := by change 3 < cp.length at hb; omega
  have hpath : IsCriticalPathOffset Γ cp (cp.length-2) preterminal :=
    ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩
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
    exact action_preserves_quotient_image_of_normalizer P U Z I hPU hZI inf_le_left
      action hact lift hnormI
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
  rw [hactorNative,MonoidHom.map_zpowers] at hlineImage
  rw [hlineImage] at hline
  have hRU : R≤U := by
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((Subgroup.zpowers_le.mpr actor.property).trans hPU)
  have hnotplane : ¬ R ≤ ZAt Γ penultimate := by
    intro hplane
    let line := commutatorAction (Subgroup.zpowers (action actor)) W
    let support := commutatorAction factor W
    let movedFactor := factor.conjBy (conjugator:action.range)
    have hconjSupport : support.map
        ((conjugator:action.range):MulAut W).toMonoidHom = commutatorAction movedFactor W :=
      SectionOne.RankOneThreeGroupAssembly.commutatorAction_conjBy factor (conjugator:action.range)
    have hfactorNe : factor ≠ movedFactor := by
      intro heqFactor
      apply hmove
      change support = support.map ((conjugator:action.range):MulAut W).toMonoidHom
      rw [hconjSupport,← heqFactor]
    have hdisjoint : Disjoint support
        (support.map ((conjugator:action.range):MulAut W).toMonoidHom) := by
      rw [hconjSupport]
      exact SectionOne.oneSevenFactor_support_disjoint_of_ne hyp factor movedFactor
        hfactor (hfactor.conjBy factor (conjugator:action.range)) hfactorNe
    have hlineSupport : line ≤ support := by
      change commutatorAction (Subgroup.zpowers (action actor)) W ≤ commutatorAction factor W
      rw [commutatorAction_eq_closure,Subgroup.closure_le]
      rintro point ⟨mover,vector,rfl⟩
      obtain ⟨power,hpower⟩ := mover.property
      refine Subgroup.subset_closure
        ⟨⟨(action.rangeRestrict actor)^power, factor.zpow_mem hactorFactor power⟩,
          vector,Subgroup.mem_top vector,?_⟩
      change vector⁻¹ * (mover:MulAut W) vector =
        vector⁻¹ * (((action.rangeRestrict actor)^power:action.range):MulAut W) vector
      rw [← hpower]
      rfl
    have hfixed : ∀ point ∈ line, ((conjugator:action.range):MulAut W) point = point := by
      intro point hpoint
      change point ∈ commutatorAction (Subgroup.zpowers (action actor)) W at hpoint
      rw [hlineImage] at hpoint
      obtain ⟨vector,hvector,rfl⟩ := hpoint
      have hz : (vector:G) ∈ ZAt Γ penultimate := hplane hvector
      have hzomega := (lemma_seven_three ctx.sectionSeven Γ).center_core penultimate cp.a'
        ((mem_neighborhood_iff_adjacent Γ).mpr htermAdj) hz
      have hcommute := ((mem_omegaOneCenterAmbient_iff (QAt Γ penultimate) (vector:G)).mp
        hzomega).2.2 (lift:G) hlift
      rw [← heq]
      change action lift (q vector) = q vector
      rw [hact]
      congr 1
      apply Subtype.ext
      change (lift:G)*(vector:G)*(lift:G)⁻¹ = (vector:G)
      rw [hcommute,mul_inv_cancel_right]
    have hlineMoved : line ≤ support.map ((conjugator:action.range):MulAut W).toMonoidHom := by
      intro point hpoint
      exact ⟨point,hlineSupport hpoint,hfixed point hpoint⟩
    have hlineBot : line = ⊥ := le_bot_iff.mp
      ((le_inf hlineSupport hlineMoved).trans hdisjoint.le_bot)
    have hlineCard : Nat.card line = 2 := hrank
    rw [hlineBot,Subgroup.card_bot] at hlineCard
    omega
  refine ⟨?_,hnotplane⟩
  intro point hpoint
  have hmem : q ⟨point,hRU hpoint⟩ ∈ J := hline (Subgroup.mem_map_of_mem q hpoint)
  have hpreimage : (⟨point,hRU hpoint⟩ : U) ∈ ((I.subgroupOf U).map q).comap q := hmem
  rw [Subgroup.comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr
    (Subgroup.subgroupOf_mono U hZI)] at hpreimage
  exact hpreimage

/-- The containment projection, preserving the original retained-actor interface. -/
public theorem nine_ten_transvection_displacement_le_terminal_intersection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hUcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^5)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2)
    (hIcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) : Subgroup G) = 2^3)
    (actor : GAt ctx.Γ ctx.criticalPath.a')
    (hactorFirst : (actor:G) ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a',Subgroup.zpowers (actor:G)⁆ ⊔ ZAt ctx.Γ ctx.criticalPath.a')
      (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    ⁅VAt ctx.Γ ctx.criticalPath.a',Subgroup.zpowers (actor:G)⁆ ≤
      VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ
        (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) :=
  (nine_ten_transvection_displacement_intersection_geometry ctx hb hUcard hmodel hIcard
    actor hactorFirst hindex).1

end Stellmacher.SectionNine
