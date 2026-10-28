module
public import Stellmacher.SectionEight.EightSixSelectedResidualCostSquare
public import Stellmacher.SectionEight.EightSixSelectedCoatomActionData
public import Stellmacher.SectionEight.EightSixSelectedCostResidualTransfer
public import Stellmacher.SectionEight.EightSixSelectedFixedCoreContainment
public import Theory.GroupAction.InvolutionDisplacementCard
/-!
# Uniform cost for every outside actor

In the actual selected local configuration, every A actor outside Qnext
has the same original commutator cost as the chosen minimum. Retain the
entire selected telescope and Q=O₂(L), without choosing either numerical
branch or imposing a uniformity or action-model premise.

The literal residual-fixed quotient Vnext/C has order equal to the square
of the selected cost, by the selected residual count and the exact product
identity. Every A actor has square in the actual action kernel. On an
elementary binary module an involution's displacement squared is at most
the module order. Exact C-to-Z cost transfer gives the upper bound by the
selected cost, and its original minimum property gives the reverse bound.
This supplies both the uniform cost-four claim and Stellmacher (8.6),
assertion (19), once assertion (17) fixes the high-branch cost; printed
pp.44–45 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
public theorem eight_six_selected_all_actor_costs
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
    (hQ : Q = twoCoreIn L) :
    ∀ mover : G, mover ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      mover ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        eightSixCommutatorCost ctx.Γ ctx.criticalPath mover =
          eightSixCommutatorCost ctx.Γ ctx.criticalPath actor := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let V := VAt Γ cp.firstStep
  let C := V ⊓ Subgroup.centralizer (twoResidualIn E : Set G)
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  have hAE : A ≤ E := geom.generated ▸ le_sup_left
  have hEV : E ≤ Subgroup.normalizer (V : Set G) :=
    geom.group_le.trans (stabilizer_le_normalizer_v Γ cp.firstStep)
  obtain ⟨hN,hW,action,haction,hkernel,_⟩ := eight_six_residual_fixed_quotient_module
    ctx hcenter hlength hcard data.first_commutator E geom.group_le
  let _ := hN
  let _ := hW
  let W := V ⧸ C.subgroupOf V
  have hWcard : Nat.card W = eightSixCommutatorCost ctx.Γ ctx.criticalPath actor ^ 2 := by
    have hcount := Subgroup.card_eq_card_quotient_mul_card_subgroup (C.subgroupOf V)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show C ≤ V from inf_le_left)).toEquiv]
      at hcount
    change Nat.card V = Nat.card W * Nat.card C at hcount
    have hY := eight_six_selected_residual_card_eq_twice_cost_square ctx hcenter hquot
      hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
      ha hout hlarge hmin hQ
    have hproduct := eight_six_selected_residual_card_mul_fixed ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    change Nat.card (⁅QAt Γ cp.firstStep,twoResidualIn E⁆ : Subgroup G) * Nat.card C =
      2 * Nat.card V at hproduct
    rw [hY,hcount] at hproduct
    have heq : Nat.card W * (2 * Nat.card C) =
        eightSixCommutatorCost ctx.Γ ctx.criticalPath actor ^ 2 * (2 * Nat.card C) := by
      nlinarith only [hproduct]
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (by decide : 0 < 2) Nat.card_pos) heq
  have hsquares := (eight_six_selected_coatom_action_data ctx previous D L Q hD hQ
    data E A0 actor geom ha action hkernel).2.2.2.2
  have hfixed := (eight_six_selected_fixed_core_containment ctx hcenter hquot hlength hcard
    previous D L Q hprev hD hL hQ data E A0 actor geom hcore hedge ha hout hlarge hmin).1
  intro mover hmover houtside
  let b : E := ⟨mover,hAE hmover⟩
  have hsquare : (action b)^2 = 1 := hsquares b hmover
  have hbound := MulAut.displacement_card_sq_le_card (action b) hsquare
  have hcyclic : (Subgroup.zpowers mover).subgroupOf E = Subgroup.zpowers b := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr (hAE hmover)),
      MonoidHom.map_zpowers]
    rfl
  have hJV : ⁅V,Subgroup.zpowers mover⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((Subgroup.zpowers_le.mpr (hAE hmover)).trans hEV)
  have hrel := Subgroup.relIndex_sup_right ((⁅V,Subgroup.zpowers mover⁆).subgroupOf V)
    (C.subgroupOf V)
  rw [←Subgroup.subgroupOf_sup hJV (show C ≤ V from inf_le_left),
    Subgroup.relIndex_subgroupOf (sup_le hJV inf_le_left),
    Subgroup.relIndex_subgroupOf hJV] at hrel
  have hrank : Nat.card (commutatorAction (Subgroup.zpowers (action b)) W) =
      C.relIndex (⁅V,Subgroup.zpowers mover⁆ ⊔ C) := by
    have h := Subgroup.quotient_conjugation_commutatorAction_card E V C
      (Subgroup.zpowers mover) hEV (Subgroup.zpowers_le.mpr (hAE hmover)) hN action haction
    rw [hcyclic,MonoidHom.map_zpowers] at h
    exact h.trans hrel.symm
  have htransfer := (eight_six_selected_cost_residual_transfer ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL hfixed mover hmover).2
  change Nat.card (commutatorAction (Subgroup.zpowers (action b)) W)^2 ≤ Nat.card W at hbound
  rw [hrank,←htransfer,hWcard] at hbound
  have hlower := hmin mover hmover houtside
  nlinarith
end Stellmacher.SectionEight
