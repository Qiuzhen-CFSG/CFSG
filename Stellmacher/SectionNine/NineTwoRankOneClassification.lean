module

public import Stellmacher.SectionNine.NineTwoCenterFour
public import Stellmacher.SectionNine.NineTwoCoreQuotientFromFour

/-!
# The normalized rank-one classification in Stellmacher (9.2)

The normalized two-neighbor configuration is split into the two genuine
mathematical reductions proved in the neighboring leaves. The index-two
transvection argument and original (1.7) force the initial center to have
order four; the faithful center-action and residual analysis then identifies
the ordinary local two-core quotient with `SL₂(2)`. The ambient context keeps
Hypothesis Two on `H` and transports no artificial hypothesis to the generated
subgroup.

Source: Stellmacher (9.2), printed p.48 / PDF p.38 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine

open Stellmacher.Later
open Stellmacher.SectionsFiveToSeven

universe u

/-- The normalized conditional classification used in Stellmacher (9.2). -/
public theorem nine_two_rank_one_classification
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (m : ctx.Γ.Vertex)
    (hm : m ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep)
    (hindex : QuotientCardEq (ZAt ctx.Γ ctx.criticalPath.a)
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ ZAt ctx.Γ m) 2)
    (hgenerate : QAt ctx.Γ m ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓
      GAt ctx.Γ ctx.criticalPath.firstStep) = GAt ctx.Γ ctx.criticalPath.firstStep)
    (hnot : ¬ QAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ m ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hcomm : ⁅ZAt ctx.Γ ctx.criticalPath.a,
      QAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ m⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.firstStep) :
    QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two ∧
      Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4 := by
  have hcard := nine_two_center_card_four ctx m hm hindex hgenerate hnot hcomm
  exact ⟨nine_two_core_quotient_of_card_four ctx hcard, hcard⟩

end Stellmacher.SectionNine
