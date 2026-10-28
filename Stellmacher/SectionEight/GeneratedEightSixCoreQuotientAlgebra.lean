module

public import Stellmacher.SectionEight.GeneratedEightSixEquationOneCoreTools
public import Stellmacher.SectionEight.GeneratedEightSixCoreQuotientBounds
public import Stellmacher.SectionEight.GeneratedEightSixCoreCommutatorImage

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven

universe u

public theorem generated_eight_six_core_quotient_algebra
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (D L Q : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (action : EightSixEquationOneActionData ctx.Γ ctx.criticalPath D L Q)
    (hgen : Q = (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔ D) :
    (⁅Q, QAt ctx.Γ ctx.criticalPath.firstStep⁆ ⊔ D =
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊔ D) ∧
    (⁅Q, Q⁆ ≤ D) ∧
    (∀ element ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a, element ^ 2 ∈ D) ∧
    (∀ element ∈ VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a,
      element ^ 2 ∈ D) := by
  exact ⟨generated_eight_six_core_commutator_image ctx hcenter hquot hlength hcard
    previous hprev D L Q hD hL hQ action hgen,
    eight_six_core_derived_and_squares_local ctx.toLocalContext hcenter hlength hcard
      previous hprev.1 D L Q hD hL hQ action hgen⟩

end Stellmacher.SectionEight
