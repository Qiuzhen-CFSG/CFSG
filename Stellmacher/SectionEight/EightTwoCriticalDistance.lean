module
public import Stellmacher.SectionEight.EightTwoCriticalDistanceLeTwo
public import Stellmacher.SectionEight.EightTwoCriticalDistanceNeTwo

/-!
# Critical distance one in the noncentral branch of (8.2)

In the exact local Section Eight context, a noncentral first-step center
forces the critical path to have length one. Its length is positive,
the shifted-commutator argument bounds it by two, and the central V0
Frattini argument excludes two. The conclusion follows arithmetically.

The local theorem supports generated-group consumers without an ambient
Sylow parameter. The legacy wrapper preserves the original context and
uses its exact local adapter, retaining the same graph and critical path.
Source: Stellmacher (8.2), Journal of Algebra 190 (1997), pp.37–38,
`refs/latex/stellmacher-n-group.tex`, the reductions to the final b=1 case.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven
universe u

public theorem eight_two_critical_distance_one_local
    {H : Type u} [Group H] [Finite H] {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    ctx.criticalPath.length = 1 := by
  have hpos := ctx.criticalPath.length_pos
  have hle := eight_two_critical_distance_le_two_local ctx hcenter
  have hne := eight_two_critical_distance_ne_two_local ctx hcenter
  omega

public theorem eight_two_critical_distance_one
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    ctx.criticalPath.length = 1 :=
  eight_two_critical_distance_one_local ctx.toLocalContext hcenter

end Stellmacher.SectionEight
