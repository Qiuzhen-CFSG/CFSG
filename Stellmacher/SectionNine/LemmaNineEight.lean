module

public import Stellmacher.LaterDefs

namespace Stellmacher.SectionNine

open Stellmacher.Later
open Stellmacher.SectionsFiveToSeven

universe u

/-- **Stellmacher (9.8).**  If `Z_{a'} ≤ V_{a+1}`, then the critical
distance is at most three. -/
public theorem lemma_nine_eight
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionNineContext H S0 S P1 P2)
    (hcontain : ZAt ctx.Γ ctx.criticalPath.a' ≤
      VAt ctx.Γ ctx.criticalPath.firstStep) :
    ctx.criticalPath.length ≤ 3 := by
  sorry

end Stellmacher.SectionNine
