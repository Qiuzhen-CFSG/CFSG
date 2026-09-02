module

public import Stellmacher.LaterDefs

namespace Stellmacher.SectionEight

open Stellmacher.Later
open Stellmacher.SectionsFiveToSeven

universe u

/-- **Stellmacher (8.5).**  If `Z_{a+1} ≤ Z(G_{a+1})`, then
`G_a/Q_a ≅ SL₂(2)` and the critical distance is two. -/
public theorem lemma_eight_five
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    QuotientIsModel
        (GAt ctx.Γ ctx.criticalPath.a)
        (QAt ctx.Γ ctx.criticalPath.a) SL2Two ∧
      ctx.criticalPath.length = 2 := by
  sorry

end Stellmacher.SectionEight
