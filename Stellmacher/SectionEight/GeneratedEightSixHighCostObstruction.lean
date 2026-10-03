module
public import Stellmacher.SectionEight.EightSixHighCostNeighborNormalizer
public import Stellmacher.SectionEight.GeneratedEightSixNeighborObstruction

/-!
# The high-cost ambient two-local obstruction in generated (8.6)

The actual selected high-cost configuration in the graph of the generated
join produces a nonsolvable two-local subgroup of the original ambient group.
All selected subgroup, action, and cost hypotheses are those of the local
neighbor-normalizer theorem; Hypothesis Two remains on the ambient group.

Apply the local (8.6)(c4) theorem through the graph-preserving adapter. Its
neighbor-center join has a PSL₃(2) normalizer quotient. Critical distance two
places that nontrivial join in the first-step two-core. The injective inclusion
of the generated group sends its normalizer into the ambient normalizer;
nonsolvability therefore gives an actual ambient nonsolvable two-local.

This is the case-(c) exclusion used under the N₂ hypothesis in Section 11,
from Stellmacher (8.6)(c4), Journal of Algebra 190 (1997), printed pp.44–45.
No high-cost order formula or complete numbered classification is required.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem generated_eight_six_high_cost_bad_local
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E A0 : Subgroup (P1 ⊔ P2 : Subgroup H)) (actor : (P1 ⊔ P2 : Subgroup H))
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hhigh : ∀ mover : (P1 ⊔ P2 : Subgroup H), mover ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      mover ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        8 ≤ eightSixCommutatorCost ctx.Γ ctx.criticalPath mover)
    (hQ : Q = twoCoreIn L) :
    ∃ U : Subgroup H, IsTwoLocal U ∧ ¬ Group.IsSolvable U := by
  obtain ⟨vertex, hneighbor, _, hmodel⟩ := eight_six_high_cost_neighbor_normalizer
    ctx.toLocalContext hcenter hquot hlength hcard previous D L Q hprev data
      E A0 actor geom hcore hedge hD hL hhigh hQ
  exact generated_eight_six_bad_local_of_neighbor_quotient ctx
    (by omega) vertex hneighbor hmodel

end Stellmacher.SectionEight
