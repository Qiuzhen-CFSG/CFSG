module

public import Stellmacher.SectionEight.GeneratedEightSixEquationOneSetup
public import Stellmacher.SectionEight.GeneratedEightSixUpstreamAction

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem generated_eight_six_equation_one_action
    {H : Type u} [Group H] [Finite H] {S0 : Sylow 2 H}
    {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex)
    (hprev : previous ∈ Later.Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (D L Q : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L) :
    EightSixEquationOneActionData ctx.Γ ctx.criticalPath D L Q := by
  obtain ⟨hnormal, hsylow, hfirst, hresidual⟩ :=
    generated_eight_six_upstream_action_identities ctx hcenter hquot hlength hcard
      previous hprev D L Q hD hL hQ
  exact ⟨hnormal, hsylow, hfirst, hresidual⟩

end Stellmacher.SectionEight
