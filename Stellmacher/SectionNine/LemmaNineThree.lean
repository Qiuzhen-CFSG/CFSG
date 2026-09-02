module

public import Stellmacher.LaterDefs

namespace Stellmacher.SectionNine

open Stellmacher.Later
open Stellmacher.SectionsFiveToSeven

universe u

/-- **Stellmacher (9.3).**  If the critical distance is greater than one,
all vertices in the orbit of `a` have quotient `SL₂(2)` and center of order
four. -/
public theorem lemma_nine_three
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionNineContext H S0 S P1 P2)
    (hb : 1 < ctx.criticalPath.length) :
    ∀ l : ctx.Γ.Vertex,
      IsConjugateVertex ctx.Γ ctx.criticalPath.a l →
      QuotientIsModel (GAt ctx.Γ l) (QAt ctx.Γ l) SL2Two ∧
        Nat.card (ZAt ctx.Γ l) = 4 := by
  sorry

end Stellmacher.SectionNine
