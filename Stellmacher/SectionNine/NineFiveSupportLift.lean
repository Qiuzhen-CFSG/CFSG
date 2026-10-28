module

public import Stellmacher.SectionNine.NineNextTransvectionFactor
public import Stellmacher.SectionOne.OneSevenTransvectionSupportSelection
public import Stellmacher.SectionNine.NineResidualImageOddCore
public import Stellmacher.SectionNine.NineFiveSpanAlgebra
public import Theory.GroupAction.SubgroupQuotientSupportLift

/-!
# The lifted canonical factor support for Stellmacher (9.5)

A terminal transvection selects an actual canonical Section One factor in
the faithful quotient action on V/Z. Its four-element support lifts to an
order-eight subgroup containing the center and the original commutator.
The terminal residual normalizes this lift, and distinct terminal-stabilizer
conjugates meet exactly in the center. The exact action, factor, actor
membership, and quotient-image equality remain available to the small and
large quotient-recognition arguments.

The local residual has odd image after killing the two-core, by (3.3).
The canonical support is invariant under the odd core, proving residual
normalization. Distinct canonical factor supports are disjoint by (1.7);
preimages turn their trivial intersection into the quotient kernel.
The separate neighboring-intersection theorem supplies the remaining
geometric field of `NineFiveSupportSeed`; no such field is assumed here.

Source: Stellmacher (9.5), printed pp.52–53/PDF pp.42–43 of
`refs/files/stellmacher-n-group.pdf`.
-/

open Stellmacher.Later
open scoped commutatorElement

namespace Stellmacher.SectionNine
open SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem support_lift_intersection
    {G : Type u} [Group G] [Finite G]
    (P U Z : Subgroup G) (hZU : Z ≤ U) (hPU : P ≤ Subgroup.normalizer (U : Set G))
    [hN : (Z.subgroupOf U).Normal] [IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U)]
    (action : P →* MulAut (U ⧸ Z.subgroupOf U))
    (hact : ∀ mover : P, ∀ point : U,
      action mover (QuotientGroup.mk' (Z.subgroupOf U) point) =
        QuotientGroup.mk' (Z.subgroupOf U)
          ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp (hPU mover.property) point).mp point.property⟩)
    (hyp : SectionOne.Hypotheses action.range (U ⧸ Z.subgroupOf U))
    (factor : Subgroup action.range)
    (hfactor : SectionOne.IsOneSevenFactor (V := U ⧸ Z.subgroupOf U) factor)
    (mover : P) :
    let q := QuotientGroup.mk' (Z.subgroupOf U)
    let L := ((commutatorAction factor (U ⧸ Z.subgroupOf U)).comap q).map U.subtype
    L ≠ L.map (MulAut.conj (mover : G)).toMonoidHom →
      L ⊓ L.map (MulAut.conj (mover : G)).toMonoidHom = Z := by
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  let support := commutatorAction factor (U ⧸ Z.subgroupOf U)
  let moved := support.map (action mover).toMonoidHom
  have hconj := Subgroup.lift_support_conjugate P U Z hPU action hact support mover
  dsimp only at hconj ⊢
  intro hne
  rw [hconj] at hne ⊢
  have hinf := SectionOne.oneSevenFactor_lifted_support_conjugate_inf
    hyp factor hfactor (action.rangeRestrict mover) q
      (fun heq => hne (congrArg (Subgroup.map U.subtype) heq))
  change support.comap q ⊓ moved.comap q = q.ker at hinf
  rw [← Subgroup.map_inf _ _ U.subtype U.subtype_injective, hinf,
    show q.ker = Z.subgroupOf U from QuotientGroup.ker_mk' _,
    Subgroup.map_subgroupOf_eq_of_le hZU]

public theorem nine_five_support_lift_of_factor
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) (actor : GAt ctx.Γ ctx.criticalPath.a')
    (hN : ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (VAt ctx.Γ ctx.criticalPath.a')).Normal) :
    let _ := hN
    let P := GAt ctx.Γ ctx.criticalPath.a'
    let U := VAt ctx.Γ ctx.criticalPath.a'
    let Z := ZAt ctx.Γ ctx.criticalPath.a'
    ∀ hW : IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U),
    let _ := hW
    ∀ action : P →* MulAut (U ⧸ Z.subgroupOf U),
      (∀ mover : P, ∀ point : U,
        action mover (QuotientGroup.mk' (Z.subgroupOf U) point) =
          QuotientGroup.mk' (Z.subgroupOf U)
            ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp
                (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a' mover.property)
                  point).mp point.property⟩) →
      action.ker = pCore 2 P →
      SectionOne.Hypotheses action.range (U ⧸ Z.subgroupOf U) →
    ∀ factor : Subgroup action.range,
      SectionOne.IsOneSevenFactor (V := U ⧸ Z.subgroupOf U) factor →
      action.rangeRestrict actor ∈ factor →
    ∃ support : Subgroup G,
      support ≤ U ∧ Z ≤ support ∧ QuotientCardEq support Z 4 ∧
      ⁅U, Subgroup.zpowers (actor : G)⁆ ≤ support ∧
      EAt ctx.Γ ctx.criticalPath.a' ≤ Subgroup.normalizer (support : Set G) ∧
      (support.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) =
        commutatorAction factor (U ⧸ Z.subgroupOf U) ∧
      ∀ conjugator : G, conjugator ∈ twoCoreIn (EAt ctx.Γ
        (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
          Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)) →
        support ≠ support.map (MulAut.conj conjugator⁻¹).toMonoidHom →
        support ⊓ support.map (MulAut.conj conjugator⁻¹).toMonoidHom = Z := by
  let _ := hN
  dsimp only
  intro hW
  let _ := hW
  intro action hact hkernel hyp factor hfactor hactor
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let U := VAt ctx.Γ ctx.criticalPath.a'
  let Z := ZAt ctx.Γ ctx.criticalPath.a'
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  let supportBar := commutatorAction factor (U ⧸ Z.subgroupOf U)
  let support := (supportBar.comap q).map U.subtype
  have hPU := stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a'
  obtain ⟨mover, _, hmover⟩ := lemma_seven_five_endpoint_alignment ctx.sectionSeven
    ctx.Γ ctx.criticalPath ctx.commutator_eq
  have horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep ctx.criticalPath.a' :=
    ⟨mover, hmover⟩
  have hcomm := (nine_next_center_commutator_and_kernel ctx hb _ horbit).2.1
  have hQP : QAt ctx.Γ ctx.criticalPath.a' ≤ P := by
    rw [QAt, CosetGraphContext.q, ctx.Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hZU : Z ≤ U := by
    change ZAt ctx.Γ ctx.criticalPath.a' ≤ U
    rw [← hcomm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hQP.trans hPU)
  have hbasic := Subgroup.lift_support_basic U Z hZU supportBar
  have hcyclicP : Subgroup.zpowers (actor : G) ≤ P := Subgroup.zpowers_le.mpr actor.property
  have hRU : ⁅U, Subgroup.zpowers (actor : G)⁆ ≤ U :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hcyclicP.trans hPU)
  have hmono : commutatorAction (Subgroup.zpowers (action.rangeRestrict actor))
      (U ⧸ Z.subgroupOf U) ≤ supportBar := by
    rw [commutatorAction_eq_closure]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨element, point, rfl⟩
    dsimp only [supportBar]
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure
      ⟨⟨element, (Subgroup.zpowers_le.mpr hactor) element.property⟩, point, rfl⟩
  have hcyclic : (Subgroup.zpowers (actor : G)).subgroupOf P =
      Subgroup.zpowers actor := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hcyclicP, MonoidHom.map_zpowers]
    rfl
  have himage := Subgroup.quotient_conjugation_commutatorAction_eq_image
    P U Z (Subgroup.zpowers (actor : G)) hPU hcyclicP hN action hact
  rw [hcyclic, MonoidHom.map_zpowers] at himage
  have hdisplacement : commutatorAction (Subgroup.zpowers (action actor))
      (U ⧸ Z.subgroupOf U) ≤ supportBar := by
    have hmap := commutatorAction_map_actor_subtype action.range
      (Subgroup.zpowers (action.rangeRestrict actor)) (V := U ⧸ Z.subgroupOf U)
    rw [MonoidHom.map_zpowers] at hmap
    exact hmap.le.trans hmono
  have hresidual : ⁅U, Subgroup.zpowers (actor : G)⁆ ≤ support := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hRU]
    apply Subgroup.map_mono
    apply Subgroup.map_le_iff_le_comap.mp
    rw [← himage]
    exact hdisplacement
  have hEP : EAt ctx.Γ ctx.criticalPath.a' ≤ P := by
    rw [EAt, CosetGraphContext.e, ctx.Γ.twoResidualAt_def]
    exact Subgroup.map_subtype_le _
  have hkernel' : pCore 2 P ≤ action.rangeRestrict.ker :=
    ((MonoidHom.ker_rangeRestrict action).trans hkernel).symm.le
  have hodd := nine_local_residual_image_le_oddCore ctx.toLocalContext _ _
    (ctx.Γ.adjacent_symm (nine_five_penultimate_adjacent ctx.toLocalContext))
    action.rangeRestrict action.rangeRestrict_surjective hkernel'
  have hinvariant := SectionOne.oneSevenFactor_support_oddCore_invariant factor hfactor
  have hnormal : EAt ctx.Γ ctx.criticalPath.a' ≤
      Subgroup.normalizer (support : Set G) := by
    apply Subgroup.lift_support_normalizes P U Z _ hEP hPU action hact supportBar
    intro element helement
    let oddElement : SectionOne.oddCore action.range :=
      ⟨action.rangeRestrict element, hodd (Subgroup.mem_map_of_mem _ helement)⟩
    ext point
    constructor
    · rintro ⟨source, hsource, rfl⟩
      exact (hinvariant.invariant oddElement source).mp hsource
    · intro hpoint
      refine ⟨(action element).symm point, ?_, (action element).apply_symm_apply point⟩
      apply (hinvariant.invariant oddElement ((action element).symm point)).mpr
      change (action element) ((action element).symm point) ∈ supportBar
      simpa only [MulEquiv.apply_symm_apply] using hpoint
  refine ⟨support, hbasic.1, hbasic.2.1, ?_, hresidual, hnormal,
    hbasic.2.2.2, ?_⟩
  · change Nat.card support = 4 * Nat.card Z
    rw [hbasic.2.2.1, hfactor.2.2.1]
  · intro conjugator hconjugator hne
    have hlocal := nine_five_penultimate_core_le_terminal ctx.toLocalContext hconjugator
    exact support_lift_intersection P U Z hZU hPU action hact hyp factor hfactor
      ⟨conjugator⁻¹, P.inv_mem hlocal⟩ hne

public theorem nine_five_support_lift
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) (actor : GAt ctx.Γ ctx.criticalPath.a')
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers (actor : G)⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    Nat.card (ZAt ctx.Γ ctx.criticalPath.a') = 2 ∧
    ∃ hN : ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (VAt ctx.Γ ctx.criticalPath.a')).Normal,
    let _ := hN
    let P := GAt ctx.Γ ctx.criticalPath.a'
    let U := VAt ctx.Γ ctx.criticalPath.a'
    let Z := ZAt ctx.Γ ctx.criticalPath.a'
    ∃ hW : IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U),
    let _ := hW
    ∃ action : P →* MulAut (U ⧸ Z.subgroupOf U),
      (∀ mover : P, ∀ point : U,
        action mover (QuotientGroup.mk' (Z.subgroupOf U) point) =
          QuotientGroup.mk' (Z.subgroupOf U)
            ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp
                (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a' mover.property)
                  point).mp point.property⟩) ∧
      action.ker = pCore 2 P ∧
      _root_.IsInvolution (action actor) ∧
      Nat.card (Subgroup.zpowers (action actor)) = 2 ∧
      Nat.card (commutatorAction (Subgroup.zpowers (action actor))
        (U ⧸ Z.subgroupOf U)) = 2 ∧
      SectionOne.Hypotheses action.range (U ⧸ Z.subgroupOf U) ∧
    ∃ factor : Subgroup action.range,
      SectionOne.IsOneSevenFactor (V := U ⧸ Z.subgroupOf U) factor ∧
      action.rangeRestrict actor ∈ factor ∧
    ∃ support : Subgroup G,
      support ≤ U ∧ Z ≤ support ∧ QuotientCardEq support Z 4 ∧
      ⁅U, Subgroup.zpowers (actor : G)⁆ ≤ support ∧
      EAt ctx.Γ ctx.criticalPath.a' ≤ Subgroup.normalizer (support : Set G) ∧
      (support.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) =
        commutatorAction factor (U ⧸ Z.subgroupOf U) ∧
      ∀ conjugator : G, conjugator ∈ twoCoreIn (EAt ctx.Γ
        (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
          Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)) →
        support ≠ support.map (MulAut.conj conjugator⁻¹).toMonoidHom →
        support ⊓ support.map (MulAut.conj conjugator⁻¹).toMonoidHom = Z := by
  obtain ⟨mover, _, hmover⟩ := lemma_seven_five_endpoint_alignment ctx.sectionSeven
    ctx.Γ ctx.criticalPath ctx.commutator_eq
  have horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep ctx.criticalPath.a' :=
    ⟨mover, hmover⟩
  refine ⟨(nine_next_center_commutator_and_kernel ctx hb _ horbit).1, ?_⟩
  obtain ⟨hN, hW, action, hact, hkernel, hinv, htwo, hrank, hyp, hfactor⟩ :=
    nine_next_transvection_factor ctx hb _ horbit actor hindex
  let _ := hN
  let _ := hW
  let factor := ⁅SectionOne.oddCore action.range,
      Subgroup.zpowers (action.rangeRestrict actor)⁆ ⊔
        Subgroup.zpowers (action.rangeRestrict actor)
  have hmem : action.rangeRestrict actor ∈ factor :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  exact ⟨hN, hW, action, hact, hkernel, hinv, htwo, hrank, hyp,
    factor, hfactor, hmem, nine_five_support_lift_of_factor ctx hb actor hN hW
      action hact hkernel hyp factor hfactor hmem⟩

end Stellmacher.SectionNine
