module
public import Theory.GroupAction.OddInvolutionFixedFaithful
public import Theory.GroupAction.NormalizingFixedPoints
public import Theory.GroupAction.ThreeGroupSixteenFaithful
public import Stellmacher.SectionEight.EightSixNextResidualThreeAction
public import Stellmacher.SectionEight.EightSixHighCostFixedDisplacement
/-!
# Residual actor centralizers in the high-cost quotient

Retain the actual selected high-cost configuration and the supplied literal
next-stabilizer action on Vnext/Znext, including the same normality witness,
elementary structure, conjugation formula and core kernel. For every A actor
outside Qnext, its centralizer in the full next residual image is elementary
abelian of exponent three and has order at most nine.

The selected order-four orbit image identifies the full residual image as
a three-group. Source (19) gives the outside actor's fixed subgroup order16.
The actual Frattini containment puts its square in the supplied action kernel.
An odd centralizer acts faithfully on that fixed subgroup. Preserve the
normalizing-actor invariance instance for the literal restricted action;
the faithful three-group classification on order16 then gives the result.

This is the action-image centralizer calculation of Stellmacher (8.6)(20),
printed p.45 of `refs/files/stellmacher-n-group.pdf`. Identification with
E/O₂(E) and the graph rank-three actor remain separate transfers; no raw
model or extra faithfulness premise is assumed here.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem eight_six_high_cost_residual_centralizer
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (ha : actor ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
    (hout : actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup G) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G))
    (hmin : ∀ other : G, other ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      other ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        eightSixCommutatorCost ctx.Γ ctx.criticalPath actor ≤
          eightSixCommutatorCost ctx.Γ ctx.criticalPath other)
    (hQ : Q = twoCoreIn L)
    (hhigh : ∀ mover : G, mover ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      mover ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        8 ≤ eightSixCommutatorCost ctx.Γ ctx.criticalPath mover)
    (hN : ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (VAt ctx.Γ ctx.criticalPath.firstStep)).Normal) :
    let _ := hN
    let P := GAt ctx.Γ ctx.criticalPath.firstStep
    let V := VAt ctx.Γ ctx.criticalPath.firstStep
    let Z := ZAt ctx.Γ ctx.criticalPath.firstStep
    let W := V ⧸ Z.subgroupOf V
    ∀ (_hW : IsElementaryAbelian 2 W) (action : P →* MulAut W),
      (∀ actor : P, ∀ point : V,
        action actor (QuotientGroup.mk' (Z.subgroupOf V) point) =
          QuotientGroup.mk' (Z.subgroupOf V)
            ⟨(actor:G)*(point:G)*(actor:G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp
                (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep
                  actor.property) point).mp point.property⟩) →
      pCore 2 P ≤ action.ker →
      ∀ mover : P,
        (mover:G) ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
        (mover:G) ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        let F := ((twoResidualIn P).subgroupOf P).map action
        let C := F ⊓ Subgroup.centralizer (Subgroup.zpowers (action mover) : Set (MulAut W))
        IsElementaryAbelian 3 C ∧ Nat.card C ≤ 9 := by
  classical
  let _ := hN
  dsimp only
  intro hW action haction hkernel mover hmover houtside
  let P := GAt ctx.Γ ctx.criticalPath.firstStep
  let V := VAt ctx.Γ ctx.criticalPath.firstStep
  let Z := ZAt ctx.Γ ctx.criticalPath.firstStep
  let W := V ⧸ Z.subgroupOf V
  let F := ((twoResidualIn P).subgroupOf P).map action
  let C := F ⊓ Subgroup.centralizer (Subgroup.zpowers (action mover) : Set (MulAut W))
  let U := FixedPoints.subgroup (Subgroup.zpowers (action mover)) W
  have hF : IsPGroup 3 F := eight_six_next_residual_action_is_three_group ctx hcenter hquot
    hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL hN hW action haction hkernel
  have hC : IsPGroup 3 C := hF.to_le inf_le_left
  have hCodd : Odd (Nat.card C) := by
    obtain ⟨n,hn⟩ := hC.exists_card_eq
    rw [hn]
    exact (by decide : Odd 3).pow
  have hCcentral : C ≤ Subgroup.centralizer
      (Subgroup.zpowers (action mover) : Set (MulAut W)) := inf_le_right
  let _ := hW
  have hcardFixed := (eight_six_high_cost_fixed_displacement_card ctx hcenter hquot hlength
    hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge
      hmin hQ hhigh hN hW action haction hkernel).2 mover hmover houtside
  have hAQ : VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a ≤ Q :=
    data.core_generation ▸ le_sup_of_le_left le_sup_left
  have hQtwo : IsPGroup 2 Q := by
    rw [hQ,twoCoreIn]
    exact (pCore_isPGroup (p := 2)).map _
  let _ : Fact (IsPGroup 2 Q) := ⟨hQtwo⟩
  have hsquareD : (mover:G)^2 ∈ D := data.core_frattini_le
    (Subgroup.mem_map.mpr ⟨(⟨mover,hAQ hmover⟩:Q)^2,
      pth_power_mem_frattini_of_isPGroup (p := 2) (⟨mover,hAQ hmover⟩:Q),rfl⟩)
  have hRnative : (QAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (GAt ctx.Γ ctx.criticalPath.firstStep) = pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep) := by
    change (ctx.Γ.twoCoreAt ctx.criticalPath.firstStep).subgroupOf _ = _
    rw [ctx.Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective (GAt ctx.Γ ctx.criticalPath.firstStep).subtype_injective _
  have hsquare : (action mover)^2=1 := by
    rw [←map_pow]
    apply MonoidHom.mem_ker.mp
    apply hkernel
    rw [←hRnative]
    exact (hD ▸ hsquareD).2
  have hCfaith := MulAut.odd_centralizer_fixed_action_faithful
    (action mover) hsquare C hCodd hCcentral
  let _ : IsInvariant C W U := fixedPoints_isInvariant_of_normalizing_actor
    C (Subgroup.zpowers (action mover))
    (hCcentral.trans (Subgroup.centralizer_le_normalizer _))
  let _ : IsElementaryAbelian 2 U := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun point =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 W) (point:W)) }
  have hfaithU : fixingSubgroup C (Set.univ : Set U) = ⊥ := by
    apply bot_unique
    intro c hc
    have hfix : c ∈ fixingSubgroup C (U : Set W) := by
      rw [mem_fixingSubgroup_iff]
      intro w hw
      exact congrArg Subtype.val ((mem_fixingSubgroup_iff (M := C)).mp hc
        ⟨w,hw⟩ (Set.mem_univ _))
    rw [hCfaith] at hfix
    exact hfix
  exact three_group_faithful_sixteen_is_elementary hC hcardFixed.1 hfaithU

end Stellmacher.SectionEight
