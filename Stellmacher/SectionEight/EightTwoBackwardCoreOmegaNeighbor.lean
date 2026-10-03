module
public import Stellmacher.SectionEight.EightTwoLocalQuotients
public import Stellmacher.SectionEight.EightTwoBackwardCoreIntersectionObstruction
public import Stellmacher.SectionFiveToSeven.Result7_6.LongPath
public import Stellmacher.SectionFiveToSeven.VertexLocalModule
public import Stellmacher.ElementaryAbelianMaxJMap
public import Stellmacher.SectionTwo.DihedralCoreOmegaGeneration

/-!
# The neighboring core's central involutions in Stellmacher (8.2)

The omega-center bound is retained under its exact local hypotheses:
first-step noncentrality, critical length greater than one, and normality
of the first core intersection in the initial stabilizer.

The independent core-intersection obstruction shows these hypotheses
contradictory. Its proof applies (2.5) to the native module in the smaller
normal supplement, closes under an odd complement, then under the common
Sylow subgroup. The resulting nontrivial two-group is normalized by both
vertex stabilizers, contradicting the trivial ambient two-core.
Thus the bound follows without imposing normality in the first-step
stabilizer or adding Thompson noncontainment to the local context.

This preserves the native-module envelope interface and its legacy wrapper
for Stellmacher (8.2), first containment case, journal pp.37–38,
`refs/latex/stellmacher-n-group.tex`. The independent obstruction uses
neither this omega bound nor the Hall-orbit equality that consumes it.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_two_backward_core_omega_le_neighbor_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlen : 1 < ctx.criticalPath.length)
    (hnormal : NormalIn
      (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
      (GAt ctx.Γ ctx.criticalPath.a)) :
    omegaOneCenterAmbient (QAt ctx.Γ ctx.criticalPath.firstStep) ≤
      VAt ctx.Γ ctx.criticalPath.firstStep := by
  exact (eight_two_backward_core_intersection_obstruction_local
    ctx hcenter hlen hnormal).elim

public theorem eight_two_backward_core_omega_le_neighbor
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlen : 1 < ctx.criticalPath.length)
    (hnormal : NormalIn
      (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
      (GAt ctx.Γ ctx.criticalPath.a)) :
    omegaOneCenterAmbient (QAt ctx.Γ ctx.criticalPath.firstStep) ≤
      VAt ctx.Γ ctx.criticalPath.firstStep := by
  exact eight_two_backward_core_omega_le_neighbor_local
    ctx.toLocalContext hcenter hlen hnormal

end Stellmacher.SectionEight
