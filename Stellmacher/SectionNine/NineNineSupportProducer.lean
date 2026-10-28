module
public import Stellmacher.SectionNine.NineNineTransvection
public import Stellmacher.SectionNine.NineNextTransvectionFactor
public import Stellmacher.SectionOne.OneSevenRankOneSupport
public import Theory.GroupAction.SubgroupQuotientSupportLift

/-!
# The lifted rank-one support in Stellmacher (9.9)

Under the reversed core containment from (9.8), an actual subgroup of the
terminal module has commutator with the initial center equal to the
first-step center. Its commutator with the terminal stabilizer's centralizer
of the initial center lies in the join of the first-step and terminal centers.
These are the two clauses of source relation (1). The stronger data
form also retains both center-line containments and the quotient support of order four,
needed in the later index argument; the original wrapper keeps its statement.

The initial transvection acts on the literal quotient V/Z. The proved (1.7)
rank-one offender theorem selects a four-element support with nonzero
restricted displacement and controls every actor fixing its commutator line.
Lift this support by taking its full inverse image in V. The full ambient
commutator is bounded by the order-two first-step center; nonzero quotient
displacement gives equality. Centralizing the initial center fixes the line,
and pulling the quotient bound back through the exact center kernel yields
the required ambient join bound. The action and normality instances are kept
unchanged throughout.

Source: Stellmacher (9.9)(1), printed p.56/PDF p.46 of
`refs/files/stellmacher-n-group.pdf`. The upstream core containment remains
explicit; the maximal-subgroup identity and terminal normalizer argument
are separate steps of the numbered theorem.
-/

open scoped commutatorElement
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem support_of_involution
    {K W : Type u} [Group K] [Finite K] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] [MulDistribMulAction K W]
    (hyp : SectionOne.Hypotheses K W) (actor : K)
    (hinvolution : _root_.IsInvolution actor)
    (hrank : Nat.card (commutatorAction (Subgroup.zpowers actor) W) = 2) :
    ∃ factor : Subgroup K, SectionOne.IsOneSevenFactor (V := W) factor ∧
      commutatorAction (Subgroup.zpowers actor) W ≤ commutatorAction factor W ∧
      commutatorSubgroup (Subgroup.zpowers actor) W (commutatorAction factor W) =
        commutatorAction (Subgroup.zpowers actor) W ∧
      ∀ mover : K,
        (∀ point ∈ commutatorAction (Subgroup.zpowers actor) W, mover • point = point) →
        ∀ point ∈ commutatorAction factor W,
          point⁻¹ * (mover • point) ∈ commutatorAction (Subgroup.zpowers actor) W := by
  classical
  let _ : Nontrivial W := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hsub
    let _ := hsub
    have hbot : commutatorAction (Subgroup.zpowers actor) W = ⊥ := Subsingleton.elim _ _
    have hone := Subgroup.card_eq_one.mpr hbot
    omega
  let Y := Subgroup.zpowers actor
  change Nat.card (commutatorAction Y W) = 2 at hrank
  have hcard : Nat.card Y = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hinvolution.2 hinvolution.1]
  let _ : IsElementaryAbelian 2 Y := IsElementaryAbelian.zpowers_of_pow_eq_one hinvolution.2
  obtain ⟨sylow, hle⟩ := IsPGroup.exists_le_sylow (IsElementaryAbelian.isPGroup 2 Y)
  let generator : Y := ⟨actor, Subgroup.mem_zpowers actor⟩
  have hgenerator : generator ≠ 1 ∧ generator ^ 2 = 1 :=
    ⟨fun heq => hinvolution.1 (congrArg Subtype.val heq), Subtype.ext hinvolution.2⟩
  obtain ⟨hcount, hfixed⟩ := card_two_action_fixed_commutator_card_data
    (U := W) generator hgenerator hcard
  have hindex : Nat.card W = 2 * Nat.card (FixedPoints.subgroup Y W) := by
    simpa only [hrank, Nat.mul_comm] using hcount
  have hA := (SectionOne.oneA_of_quadratic_fixed_index_two hyp sylow Y hle hindex hfixed).1
  exact SectionOne.oneSeven_support_of_rank_one_offender_with_line hyp sylow Y hA hrank

public theorem nine_nine_support_data_with_line_of_terminal_core
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hcore : VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep) :
    ∃ support : Subgroup G,
      support ≤ VAt ctx.Γ ctx.criticalPath.a' ∧
      ZAt ctx.Γ ctx.criticalPath.a' ≤ support ∧
      QuotientCardEq support (ZAt ctx.Γ ctx.criticalPath.a') 4 ∧
      ZAt ctx.Γ ctx.criticalPath.firstStep ≤ support ∧
      ⁅support, ZAt ctx.Γ ctx.criticalPath.a⁆ = ZAt ctx.Γ ctx.criticalPath.firstStep ∧
      ⁅support, GAt ctx.Γ ctx.criticalPath.a' ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G)⁆ ≤
          ZAt ctx.Γ ctx.criticalPath.firstStep ⊔ ZAt ctx.Γ ctx.criticalPath.a' := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a'
  let U := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let R := ZAt Γ cp.firstStep
  let Za := ZAt Γ cp.a
  have hfour := (lemma_nine_three_ambient ctx hb cp.a ⟨1, Γ.act_one _⟩).2
  have hfull : ⁅U, Za⁆ = R := by
    rw [Subgroup.commutator_comm]
    exact nine_nine_commutator_eq_of_initial_four ctx hcore hfour
  have hRcard : Nat.card R = 2 :=
    (nine_next_center_and_commutator_of_initial_four ctx.toLocalContext hfour
      cp.firstStep ⟨1, Γ.act_one _⟩).1
  have hactionData := nine_nine_terminal_action_of_core ctx.toLocalContext hcore
  have hRU : R ≤ U := by
    rw [← hfull, Subgroup.commutator_comm]
    exact hactionData.2.2.2.1.trans inf_le_right
  have hRZa : R ≤ Za := by
    rw [← hfull, Subgroup.commutator_comm]
    exact hactionData.2.2.2.1.trans inf_le_left
  obtain ⟨mover, _, hmover⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have horbit : IsConjugateVertex Γ cp.firstStep cp.a' := ⟨mover, hmover⟩
  obtain ⟨actor, hactorZa, hactorNot, hactorComm, hindex⟩ :=
    nine_nine_initial_transvection ctx hb hcore
  obtain ⟨hN, hW, action, hact, hkernel, hinv, htwo, hrank, hyp, _⟩ :=
    nine_next_transvection_factor ctx hb cp.a' horbit actor hindex
  let _ := hN
  let _ := hW
  let W := U ⧸ Z.subgroupOf U
  let q : U →* W := QuotientGroup.mk' (Z.subgroupOf U)
  let induced := action.rangeRestrict actor
  let Y := Subgroup.zpowers induced
  have hinduced : _root_.IsInvolution induced :=
    ⟨fun heq => hinv.1 (congrArg Subtype.val heq), Subtype.ext hinv.2⟩
  have hrankY : Nat.card (commutatorAction Y W) = 2 := by
    rw [← commutatorAction_map_actor_subtype action.range Y, MonoidHom.map_zpowers]
    exact hrank
  obtain ⟨factor, hfactor, hlineSupport, hrestricted, hcontrol⟩ :=
    support_of_involution hyp induced hinduced hrankY
  let supportBar := commutatorAction factor W
  let support := (supportBar.comap q).map U.subtype
  have hcomm := (nine_next_center_commutator_and_kernel ctx hb cp.a' horbit).2.1
  have hQP : QAt Γ cp.a' ≤ P := by
    rw [QAt, CosetGraphContext.q, Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hPU : P ≤ Subgroup.normalizer (U : Set G) := stabilizer_le_normalizer_v Γ cp.a'
  have hZU : Z ≤ U := by
    change ZAt Γ cp.a' ≤ U
    rw [← hcomm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hQP.trans hPU)
  have hbasic := Subgroup.lift_support_basic U Z hZU supportBar
  change support ≤ U ∧ Z ≤ support ∧
    Nat.card support = Nat.card supportBar * Nat.card Z ∧
    (support.subgroupOf U).map q = supportBar at hbasic
  have hline : commutatorAction Y W = (R.subgroupOf U).map q := by
    rw [← commutatorAction_map_actor_subtype action.range Y, MonoidHom.map_zpowers]
    have hcyclic : (Subgroup.zpowers (actor : G)).subgroupOf P =
        Subgroup.zpowers actor := by
      apply Subgroup.map_injective P.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr actor.property),
        MonoidHom.map_zpowers]
      rfl
    have himage := Subgroup.quotient_conjugation_commutatorAction_eq_image
      P U Z (Subgroup.zpowers (actor : G)) hPU
      (Subgroup.zpowers_le.mpr actor.property) hN action hact
    rw [hcyclic, MonoidHom.map_zpowers, hactorComm] at himage
    exact himage
  have hRsupport : R ≤ support := by
    intro point hpoint
    refine ⟨⟨point, hRU hpoint⟩, ?_, rfl⟩
    change q ⟨point, hRU hpoint⟩ ∈ supportBar
    apply hlineSupport
    rw [hline]
    exact Subgroup.mem_map_of_mem q hpoint
  have hbound : ⁅support, Za⁆ ≤ R :=
    (Subgroup.commutator_mono hbasic.1 le_rfl).trans_eq hfull
  have hnonzero : ⁅support, Za⁆ ≠ ⊥ := by
    intro hzero
    have hfixedSupport : ∀ mover : Y, ∀ point ∈ supportBar, mover • point = point := by
      intro mover point hpoint
      have hYeq : Y = (Subgroup.zpowers actor).map action.rangeRestrict :=
        (MonoidHom.map_zpowers action.rangeRestrict actor).symm
      have hmover : (mover : action.range) ∈
          (Subgroup.zpowers actor).map action.rangeRestrict :=
        hYeq ▸ mover.property
      obtain ⟨localMover, hlocalMover, heqMover⟩ := hmover
      have hlocalZa : (localMover : G) ∈ Za :=
        (Subgroup.zpowers_le.mpr hactorZa : Subgroup.zpowers actor ≤ Za.subgroupOf P) hlocalMover
      rw [← hbasic.2.2.2] at hpoint
      obtain ⟨lift, hlift, rfl⟩ := hpoint
      have hcommute := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hzero
        hlift (localMover : G) hlocalZa
      change ((mover : action.range) : MulAut W) (q lift) = q lift
      rw [← heqMover]
      change action localMover (q lift) = q lift
      rw [hact]
      congr 1
      apply Subtype.ext
      change (localMover : G) * (lift : G) * (localMover : G)⁻¹ = (lift : G)
      change (localMover : G) * (lift : G) = (lift : G) * (localMover : G) at hcommute
      rw [hcommute, mul_inv_cancel_right]
    have hbot : commutatorSubgroup Y W supportBar = ⊥ := by
      apply le_bot_iff.mp
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨mover, point, hpoint, rfl⟩
      change point⁻¹ * (mover • point) = 1
      rw [hfixedSupport mover point hpoint, inv_mul_cancel]
    rw [hrestricted] at hbot
    have hcard : Nat.card (commutatorAction Y W) = 1 := Subgroup.card_eq_one.mpr hbot
    omega
  have hsupportComm : ⁅support, Za⁆ = R := by
    have hh := (Subgroup.one_lt_card_iff_ne_bot _).mpr hnonzero
    exact Subgroup.eq_of_le_of_card_ge hbound (by omega)
  refine ⟨support, hbasic.1, hbasic.2.1, ?_, hRsupport, hsupportComm, ?_⟩
  · change Nat.card support = 4 * Nat.card Z
    rw [hbasic.2.2.1, hfactor.2.2.1]
  · apply Subgroup.commutator_le.mpr
    intro point hpoint mover hmover
    let localMover : P := ⟨mover, hmover.1⟩
    let pointU : U := ⟨point, hbasic.1 hpoint⟩
    have hpointBar : q pointU⁻¹ ∈ supportBar := by
      rw [← hbasic.2.2.2]
      exact Subgroup.mem_map_of_mem q (support.inv_mem hpoint)
    have hfixedLine : ∀ vector ∈ commutatorAction Y W,
        action.rangeRestrict localMover • vector = vector := by
      intro vector hvector
      rw [hline] at hvector
      obtain ⟨lift, hlift, rfl⟩ := hvector
      change action localMover (q lift) = q lift
      rw [hact]
      congr 1
      apply Subtype.ext
      have hcommute := Subgroup.mem_centralizer_iff.mp hmover.2 (lift : G) (hRZa hlift)
      change mover * (lift : G) * mover⁻¹ = (lift : G)
      rw [← hcommute, mul_inv_cancel_right]
    have hdelta := hcontrol (action.rangeRestrict localMover) hfixedLine
      (q pointU⁻¹) hpointBar
    have hcommU : ⁅point, mover⁆ ∈ U :=
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hPU)
        (Subgroup.commutator_mem_commutator (hbasic.1 hpoint) hmover.1)
    have hdeltaEq : (q pointU⁻¹)⁻¹ * (action.rangeRestrict localMover • q pointU⁻¹) =
        q ⟨⁅point, mover⁆, hcommU⟩ := by
      change (q pointU⁻¹)⁻¹ * action localMover (q pointU⁻¹) = _
      rw [hact, ← map_inv, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, commutatorElement_def,
        pointU, localMover, mul_assoc]
    rw [hdeltaEq, hline] at hdelta
    have hpreimage : (⟨⁅point, mover⁆, hcommU⟩ : U) ∈
        ((R.subgroupOf U).map q).comap q := hdelta
    rw [Subgroup.comap_map_eq, show q.ker = Z.subgroupOf U from QuotientGroup.ker_mk' _,
      ← Subgroup.subgroupOf_sup hRU hZU] at hpreimage
    exact hpreimage

public theorem nine_nine_support_data_of_terminal_core
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hcore : VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep) :
    ∃ support : Subgroup G,
      support ≤ VAt ctx.Γ ctx.criticalPath.a' ∧
      ZAt ctx.Γ ctx.criticalPath.a' ≤ support ∧
      QuotientCardEq support (ZAt ctx.Γ ctx.criticalPath.a') 4 ∧
      ⁅support, ZAt ctx.Γ ctx.criticalPath.a⁆ = ZAt ctx.Γ ctx.criticalPath.firstStep ∧
      ⁅support, GAt ctx.Γ ctx.criticalPath.a' ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G)⁆ ≤
          ZAt ctx.Γ ctx.criticalPath.firstStep ⊔ ZAt ctx.Γ ctx.criticalPath.a' := by
  obtain ⟨support, hle, hcenter, hcard, _, hcomm, hcentral⟩ :=
    nine_nine_support_data_with_line_of_terminal_core ctx hb hcore
  exact ⟨support, hle, hcenter, hcard, hcomm, hcentral⟩

public theorem nine_nine_support_of_terminal_core
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hcore : VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep) :
    ∃ support : Subgroup G,
      support ≤ VAt ctx.Γ ctx.criticalPath.a' ∧
      ⁅support, ZAt ctx.Γ ctx.criticalPath.a⁆ = ZAt ctx.Γ ctx.criticalPath.firstStep ∧
      ⁅support, GAt ctx.Γ ctx.criticalPath.a' ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G)⁆ ≤
          ZAt ctx.Γ ctx.criticalPath.firstStep ⊔ ZAt ctx.Γ ctx.criticalPath.a' := by
  obtain ⟨support, hle, _, _, hcomm, hcentral⟩ :=
    nine_nine_support_data_of_terminal_core ctx hb hcore
  exact ⟨support, hle, hcomm, hcentral⟩

end Stellmacher.SectionNine