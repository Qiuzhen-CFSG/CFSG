module
public import Stellmacher.SectionEight.EightSixHighCostResidualElementary
public import Stellmacher.SectionEight.EightSixHighCostActorRank
public import Stellmacher.SectionEight.EightSixNextActionKernel
/-!
# The actual elementary high-cost residual module

The selected high-cost graph configuration, including elementary D from
common structure, supplies a literal next-stabilizer action on Vnext/Znext.
Its kernel is exactly the next two-core and its full residual image is
an elementary abelian three-group. The normality and action witnesses are
retained, with the conjugation formula on actual quotient representatives.

The graph actor-rank theorem gives the required order-eight actor quotient
from the original local geometry. The next quotient-module factory gives
the action, and source-(20) centralizers then yield its elementary residual
image. Source (18) identifies Vnext with the next core; the Frattini-kernel
transfer upgrades the factory's core containment to exact kernel equality.

This assembles the elementary-image assertion of Stellmacher (8.6)(21),
printed p.45. It adds no assumed actor rank or faithfulness. The native
E/O₂(E) identification and the later four-factor order count are separate
consumers of this packet.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
public theorem eight_six_high_cost_residual_module_data
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
    (helementary : IsElementaryAbelianSubgroup 2 D)
    : ∃ hN : ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (VAt ctx.Γ ctx.criticalPath.firstStep)).Normal,
    let _ := hN
    let P := GAt ctx.Γ ctx.criticalPath.firstStep
    let V := VAt ctx.Γ ctx.criticalPath.firstStep
    let Z := ZAt ctx.Γ ctx.criticalPath.firstStep
    let W := V ⧸ Z.subgroupOf V
    ∃ _hW : IsElementaryAbelian 2 W, ∃ action : P →* MulAut W,
      (∀ actor : P, ∀ point : V,
        action actor (QuotientGroup.mk' (Z.subgroupOf V) point) =
          QuotientGroup.mk' (Z.subgroupOf V)
            ⟨(actor:G)*(point:G)*(actor:G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp
                (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep
                  actor.property) point).mp point.property⟩) ∧
      action.ker = pCore 2 P ∧
      IsElementaryAbelian 3 (((twoResidualIn P).subgroupOf P).map action) := by
  have hindex := eight_six_high_cost_actor_rank ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh helementary
  obtain ⟨hN,hW,action,hformula,hkernel,_⟩ :=
    eight_six_next_quotient_module_data_local ctx hcenter hlength hcard data.first_commutator
  have h := eight_six_high_cost_residual_action_is_elementary ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hhigh hindex
    hN hW action hformula hkernel
  have hselected := eight_six_selected_fixed_core_containment ctx hcenter hquot hlength
    hcard previous D L Q hprev hD hL hQ data E A0 actor geom hcore hedge ha hout hlarge hmin
  have hRV := eight_six_high_cost_next_core_eq_v ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL hhigh hselected.1 helementary
  have hkernelEq := eight_six_next_quotient_action_kernel_of_core_eq_v ctx hRV
    data.first_commutator hN action hformula hkernel
  exact ⟨hN,hW,action,hformula,hkernelEq,h⟩
end Stellmacher.SectionEight
