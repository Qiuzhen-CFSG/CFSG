module
public import Stellmacher.LaterDefs
public import Stellmacher.SectionEight.EightTwoCriticalDistance
public import Stellmacher.SectionEight.EightTwoDistanceOneClassification

/-!
# Stellmacher (8.2): the noncentral stabilizer classification

If the first-step vertex center is not central in its stabilizer, every
vertex stabilizer in the local Section Eight graph is isomorphic to S4
or C2 times S4. These are models of the whole stabilizers.

The critical-distance theorem combines the backward commutator and V0
Frattini contradictions to force distance one. The distance-one classifier
then proves elementary cores, their central decomposition and size bounds,
and uses actual critical-edge involutions outside the cores to identify
the two distinguished stabilizers. Vertex conjugacy propagates the result.
The outside involution input retains the splitting information needed by
the finite-group classification.

The local theorem works with the exact local context, including generated
groups. The original public theorem keeps its ambient context and supplied
Sylow parameter through the existing adapter, with identical graph and path.
Source: Stellmacher (8.2), Journal of Algebra 190 (1997), printed pp.37–38,
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven
universe u

public theorem lemma_eight_two_local
    {H : Type u} [Group H] [Finite H] {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    ∀ d : ctx.Γ.Vertex,
      IsModel (GAt ctx.Γ d) S4 ∨ IsModel (GAt ctx.Γ d) (C2 × S4) :=
  eight_two_models_of_distance_one_local ctx hcenter
    (eight_two_critical_distance_one_local ctx hcenter)

/-- **Stellmacher (8.2).** If `Z_{a+1} \nleq Z(G_{a+1})`, every vertex
stabilizer has one of the two displayed isomorphism types. -/
public theorem lemma_eight_two
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    ∀ d : ctx.Γ.Vertex,
      IsModel (GAt ctx.Γ d) S4 ∨
        IsModel (GAt ctx.Γ d) (C2 × S4) :=
  lemma_eight_two_local ctx.toLocalContext hcenter

end Stellmacher.SectionEight
