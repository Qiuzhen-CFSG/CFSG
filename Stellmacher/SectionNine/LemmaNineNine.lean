module

public import Stellmacher.LaterDefs

namespace Stellmacher.SectionNine

open Stellmacher.Later
open Stellmacher.SectionsFiveToSeven

universe u

/-- **Stellmacher (9.9).**  If `Z_{a+1} ≤ V_{a'}`, then the critical
distance is at most three. -/
public theorem lemma_nine_nine
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionNineContext H S0 S P1 P2)
    (hcontain : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      VAt ctx.Γ ctx.criticalPath.a') :
    ctx.criticalPath.length ≤ 3 := by
  sorry

end Stellmacher.SectionNine
