module

public import Stellmacher.LaterDefs

open scoped BigOperators Pointwise

namespace Stellmacher.SectionNine

open Stellmacher.Later
open Stellmacher.SectionsFiveToSeven

universe u

/-- **Stellmacher (9.4).**  The local subgroup `A` is forced into
`V_{a+1}` by the three displayed commutator, generation, and index
hypotheses. -/
public theorem lemma_nine_four
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionNineContext H S0 S P1 P2)
    (hb : 1 < ctx.criticalPath.length)
    (r : ctx.Γ.Vertex)
    (hr : ctx.Γ.distance r ctx.criticalPath.firstStep = 2)
    (t : H)
    (ht : t ∈ GAt ctx.Γ ctx.criticalPath.firstStep ∧
      t ∈ Subgroup.centralizer (VAt ctx.Γ r : Set H))
    (x : H)
    (hx : x ∈ ⁅EAt ctx.Γ ctx.criticalPath.firstStep, Subgroup.zpowers t⁆)
    (A : Subgroup H)
    (hA : A ≤ VAt ctx.Γ (ctx.Γ.act x r))
    (h1 : ⁅A, Subgroup.zpowers t⁆ ≤
      VAt ctx.Γ ctx.criticalPath.firstStep)
    (h2 : ∀ n : ctx.Γ.Vertex,
      n ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep →
      n ∈ Neighborhood ctx.Γ (ctx.Γ.act x r) →
      (GAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ n) ⊔
        Subgroup.zpowers t = GAt ctx.Γ ctx.criticalPath.firstStep)
    (h3 : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.firstStep, Subgroup.zpowers t⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.firstStep)
      (ZAt ctx.Γ ctx.criticalPath.firstStep) 2) :
    A ≤ VAt ctx.Γ ctx.criticalPath.firstStep := by
  sorry

end Stellmacher.SectionNine
