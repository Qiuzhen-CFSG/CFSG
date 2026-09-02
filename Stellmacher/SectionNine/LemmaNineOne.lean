module

public import Stellmacher.LaterDefs

open scoped BigOperators Pointwise

namespace Stellmacher.SectionNine

open Stellmacher.Later
open Stellmacher.SectionsFiveToSeven

universe u

/-- **Stellmacher (9.1).**  In the case `b=1`, define
`V_{a'}^* = ⟨(Z_a ∩ Q_{a'})^{G_{a'}}⟩`; the three conclusions are recorded
 with the source's semidirect-product and central-product notation. -/
public theorem lemma_nine_one
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionNineContext H S0 S P1 P2)
    (hb : ctx.criticalPath.length = 1) :
    let Vstar := conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a')
    QuotientIsSemidirectModel
          (GAt ctx.Γ ctx.criticalPath.a)
          (QAt ctx.Γ ctx.criticalPath.a) SL2Two C2 ∧
      QuotientIsModel
          (GAt ctx.Γ ctx.criticalPath.a')
          (QAt ctx.Γ ctx.criticalPath.a') SL2Two ∧
      Nat.card S = 2 ^ 7 ∧
      QAt ctx.Γ ctx.criticalPath.a = ZAt ctx.Γ ctx.criticalPath.a ∧
      IsCentralProductQ8Q8 Vstar ∧
      ∃ U : Subgroup H,
        U ≤ Vstar ∧ Nat.card U = 2 ^ 3 ∧
        QuotientIsModel (Subgroup.normalizer (U : Set H)) U L3Two := by
  sorry

end Stellmacher.SectionNine
