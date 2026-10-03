module
public import Stellmacher.SectionEight.EightSixDefs
public import Stellmacher.SectionEight.EightSixHighCostResidualRankFour
public import Stellmacher.SectionEight.EightSixHighCostCoreOrders
public import Stellmacher.SectionEight.EightSixHighCostCoreActionRank
public import Stellmacher.SectionEight.EightSixHighCostFixedCoreSplitting
public import Stellmacher.SectionEight.EightSixHighCostInvolutionLift
public import Stellmacher.SectionEight.EightSixHighCostNeighborNormalizer
public import Stellmacher.SectionEight.EightSixHighCostSylowOrders
public import Stellmacher.SectionEight.EightSixHighCostOrderThreeFixedFree
/-!
# The complete high-cost alternative in Stellmacher (8.6)

The selected high-cost configuration, with elementary opposite-core
intersection D, yields the exact case-C constructor of the canonical
`LemmaEightSixAlternative`. The prescribed Sylow three-subgroup T is retained.
This is the branch assembly consumed by the numbered theorem; the common
base conclusions are supplied separately by `EightSixCommonStructure`.

The Sylow-order bounds and residual rank-four theorem give the first numerical
fields. The core-order, direct-product, extraspecial and core-action results
supply c1 and c2. The two native quotient-action theorems supply c3 with the
user-approved interpretation: fixed cosets for each invariant cubic quotient,
and a suitable representative of each quotient involution. The neighbor
normalizer theorem supplies c4. Every local theorem is applied through the
canonical context's `toLocalContext`, preserving the graph and critical path.

Source: Stellmacher, (8.6)(c), printed p.41, and its proof, pp.44–45.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem eight_six_high_cost_case_c
    {G : Type u} [Group G] [Finite G] {S0 : Sylow 2 G} {S P1 P2 : Subgroup G}
    (ctx : SectionEightContext G S0 S P1 P2)
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
    (T : Subgroup G) (hT : IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    :
    LemmaEightSixAlternative ctx previous D L Q T := by
  have hsylow := eight_six_high_cost_sylow_card_bounds ctx.toLocalContext hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh helementary
  have hcubic := eight_six_high_cost_order_three_fixed_point_free ctx.toLocalContext hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh helementary
  have hres := eight_six_high_cost_residual_quotient_rank_four ctx.toLocalContext hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh helementary
  have horders := eight_six_high_cost_core_orders ctx.toLocalContext hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh helementary
  have hsplit := eight_six_high_cost_fixed_core_splitting ctx.toLocalContext hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh helementary T hT
  have hextra := eight_six_high_cost_next_core_extraspecial ctx.toLocalContext hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh helementary
  have hcoreRank := eight_six_high_cost_core_action_rank ctx.toLocalContext hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh helementary
  have hinvol := eight_six_high_cost_quotient_involution_centralizes ctx.toLocalContext hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL
    ha hout hlarge hmin hQ hhigh helementary
  have hnormalizer := eight_six_high_cost_neighbor_normalizer ctx.toLocalContext
    hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge
    hD hL hhigh hQ
  have hnextcard : Nat.card (QAt ctx.Γ ctx.criticalPath.firstStep) = 512 := hextra.2
  apply LemmaEightSixAlternative.c hsylow hquot hres _ _ hcubic hinvol hnormalizer
  · exact ⟨by simpa only [show (2:ℕ)^6=64 from by decide] using horders.1,
      by simpa only [show (2:ℕ)^5=32 from by decide] using horders.2,hcard,hsplit⟩
  · exact ⟨hextra.1,by simpa only [show (2:ℕ)^9=512 from by decide] using hnextcard,hcoreRank⟩
end Stellmacher.SectionEight
