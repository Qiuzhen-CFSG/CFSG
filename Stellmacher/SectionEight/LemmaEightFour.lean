module

public import Stellmacher.LaterDefs

namespace Stellmacher.SectionEight

open Stellmacher.Later
open Stellmacher.SectionsFiveToSeven

universe u

/-- **Stellmacher (8.4).**  The subgroup
`Z=C_{Z_a}(J(Z_a,\bar S))` is normal in `G_{a+1}` under the hypothesis of
(8.2). -/
public theorem lemma_eight_four
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    NormalIn
      (ZAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (LocalJ (ZAt ctx.Γ ctx.criticalPath.a)
          (S : Subgroup H) : Set H))
      (GAt ctx.Γ ctx.criticalPath.firstStep) := by
  sorry

end Stellmacher.SectionEight
