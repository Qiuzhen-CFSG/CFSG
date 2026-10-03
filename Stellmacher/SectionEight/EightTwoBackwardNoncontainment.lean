module
public import Stellmacher.SectionEight.EightTwoBackwardContainmentCore
public import Stellmacher.SectionEight.EightTwoBackwardTranslateNormality
public import Stellmacher.SectionEight.EightTwoBackwardCoreIntersectionObstruction

/-!
# Backward-neighbor noncontainment in Stellmacher (8.2)

In the noncentral first-step case, a neighbor m whose edge stabilizer
and the opposite vertex center generate the initial stabilizer cannot
have its center contained in the opposite stabilizer. The local theorem
uses the actual Section Seven graph and the native (6.3) quotient data;
the legacy theorem keeps its exact signature through `toLocalContext`.

Assumed containment gives critical length greater than one and normality
of the first-edge core intersection in the initial stabilizer. The native
core-intersection obstruction contradicts these two facts: it applies (2.5)
to the actual smaller normal supplement, using its exact supplied Sylow.
Taking the Hall orbit of that Sylow-center module and then its conjugate
closure under the common Sylow produces a two-subgroup normalized by both
generating vertex stabilizers, contrary to their trivial ambient two-core.
Its nontriviality comes from the initial vertex center.
No identification of the native module with a graph vertex module is needed.

Source: Stellmacher (8.2), first containment case, Journal of Algebra 190
(1997), printed pp.37–38, refs/latex/stellmacher-n-group.tex. This result
feeds the separate backward critical-pair shift. The original imports and
legacy public interface are retained for existing consumers.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_two_backward_neighbor_not_le_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (m : ctx.Γ.Vertex) (hm : m ∈ neighborhood ctx.Γ ctx.criticalPath.a)
    (hgen : (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ m) ⊔
      ZAt ctx.Γ ctx.criticalPath.a' = GAt ctx.Γ ctx.criticalPath.a) :
    ¬ ZAt ctx.Γ m ≤ GAt ctx.Γ ctx.criticalPath.a' := by
  intro hcontained
  obtain ⟨hlen, hnormal⟩ :=
    eight_two_core_intersection_normal_of_backward_containment_local
      ctx hcenter m hm hgen hcontained
  exact eight_two_backward_core_intersection_obstruction_local ctx hcenter hlen hnormal

public theorem eight_two_backward_neighbor_not_le
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (m : ctx.Γ.Vertex) (hm : m ∈ neighborhood ctx.Γ ctx.criticalPath.a)
    (hgen : (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ m) ⊔
      ZAt ctx.Γ ctx.criticalPath.a' = GAt ctx.Γ ctx.criticalPath.a) :
    ¬ ZAt ctx.Γ m ≤ GAt ctx.Γ ctx.criticalPath.a' := by
  exact eight_two_backward_neighbor_not_le_local ctx.toLocalContext hcenter m hm hgen

end Stellmacher.SectionEight
