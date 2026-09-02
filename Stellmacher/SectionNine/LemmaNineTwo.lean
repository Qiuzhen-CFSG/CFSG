module

public import Stellmacher.LaterDefs

open scoped BigOperators Pointwise

namespace Stellmacher.SectionNine

open Stellmacher.Later
open Stellmacher.SectionsFiveToSeven

universe u

/-- **Stellmacher (9.2).**  The local quotient and center order conclusion
under the stated two-neighbor hypotheses. -/
public theorem lemma_nine_two
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionNineContext H S0 S P1 P2)
    (d l m : ctx.Γ.Vertex)
    (hd : IsConjugateVertex ctx.Γ ctx.criticalPath.a' d)
    (hl : l ∈ Neighborhood ctx.Γ d)
    (hm : m ∈ Neighborhood ctx.Γ d)
    (hindex : QuotientCardEq
      (ZAt ctx.Γ l) (ZAt ctx.Γ l ⊓ ZAt ctx.Γ m) 2)
    (hgenerate : QAt ctx.Γ m ⊔
      (GAt ctx.Γ l ⊓ GAt ctx.Γ d) = GAt ctx.Γ d) :
    QuotientIsModel (GAt ctx.Γ l) (QAt ctx.Γ l) SL2Two ∧
      Nat.card (ZAt ctx.Γ l) = 4 := by
  sorry

end Stellmacher.SectionNine
