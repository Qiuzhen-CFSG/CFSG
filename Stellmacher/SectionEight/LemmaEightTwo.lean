module

public import Stellmacher.LaterDefs

namespace Stellmacher.SectionEight

open Stellmacher.Later
open Stellmacher.SectionsFiveToSeven

universe u

/-- **Stellmacher (8.2).**  If `Z_{a+1} \nleq Z(G_{a+1})`, every barred
vertex stabilizer has one of the two displayed isomorphism types. -/
public theorem lemma_eight_two
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    ∀ d : ctx.Γ.Vertex,
      QuotientIsModel
          (GAt ctx.Γ d)
          (GAt ctx.Γ d ⊓
            Subgroup.centralizer (ZAt ctx.Γ d : Set H)) S4 ∨
        QuotientIsModel
          (GAt ctx.Γ d)
          (GAt ctx.Γ d ⊓
            Subgroup.centralizer (ZAt ctx.Γ d : Set H)) (C2 × S4) := by
  sorry

end Stellmacher.SectionEight
