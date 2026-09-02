module

public import Stellmacher.LaterDefs

open scoped BigOperators Pointwise

namespace Stellmacher.SectionNine

open Stellmacher.Later
open Stellmacher.SectionsFiveToSeven

universe u

/-- **Stellmacher (9.5).**  The two possibilities for `V_{a'}` when an
involution has the prescribed transvection-sized commutator. -/
public theorem lemma_nine_five
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionNineContext H S0 S P1 P2)
    (hb : 1 < ctx.criticalPath.length)
    (aMinus2 : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath
      (ctx.criticalPath.length - 2) aMinus2)
    (t : H)
    (ht : t ∈ VAt ctx.Γ ctx.criticalPath.firstStep ∧
      t ∉ QAt ctx.Γ ctx.criticalPath.a')
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers t⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a')
      (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hcontain : ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers t⁆ ≤
      VAt ctx.Γ aMinus2) :
    (Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2 ^ 3 ∧
        QuotientIsModel
          (GAt ctx.Γ ctx.criticalPath.a')
          (QAt ctx.Γ ctx.criticalPath.a') SL2Two) ∨
      (Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2 ^ 5 ∧
        QuotientIsModel
          (GAt ctx.Γ ctx.criticalPath.a')
          (QAt ctx.Γ ctx.criticalPath.a') (SL2Two × C2) ∧
        Nat.card
          (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ aMinus2 : Subgroup H) = 2 ^ 3) := by
  sorry

end Stellmacher.SectionNine
