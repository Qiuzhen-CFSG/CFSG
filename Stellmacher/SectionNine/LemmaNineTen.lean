module

public import Stellmacher.LaterDefs

namespace Stellmacher.SectionNine

open Stellmacher.Later
open Stellmacher.SectionsFiveToSeven

universe u

/-- **Stellmacher (9.10).**  Under the standing Section 9 hypotheses, the
critical distance is at most three. -/
public theorem lemma_nine_ten
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionNineContext H S0 S P1 P2) :
    ctx.criticalPath.length ≤ 3 := by
  sorry

end Stellmacher.SectionNine
